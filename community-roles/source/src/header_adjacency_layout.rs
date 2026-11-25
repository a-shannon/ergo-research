//! Analytical parent/digest adjacency over a bounded owner-slot domain.
//!
//! This module emits gates for a future common-witness consumer and evaluates
//! their multilinear coefficients. It does not construct a proof, authenticate
//! history, check header hashes, or establish genesis ancestry.
use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    gkr::Gate,
    header_hash, header_order, segment_relation, serializer,
    transcript::Transcript,
    wiring::{self, RightIndex},
};

const LOCAL_INPUT_LOG: usize = 20;
const LOCAL_ROW_LOG: usize = 9;
const ID_BITS: usize = 256;
const MAX_SLOT_LOG: usize = 21;
const LOCAL_INPUT_WIDTH: usize = 1 << LOCAL_INPUT_LOG;
const LOCAL_ROW_WIDTH: usize = 1 << LOCAL_ROW_LOG;
const PROFILE: &[u8] = b"historical-header-parent-digest-adjacency-v1";
const METADATA_PROFILE: &[u8] = b"historical-header-metadata-adjacency-v1";
const VERSION: u64 = 1;

/// Immutable compiler-derived maps and public endpoints for one adjacency
/// relation. The intended consumer emits these terms into the same packed
/// common witness used by the header and history-owner relations.
#[derive(Clone, Debug)]
pub struct HeaderAdjacencyLayout {
    n: u64,
    slot_log: usize,
    input_log: usize,
    row_log: usize,
    input_len: usize,
    row_count: usize,
    term_count: usize,
    parent_wires: [usize; ID_BITS],
    digest_wires: [usize; ID_BITS],
    start: [u8; 32],
    tip: [u8; 32],
    profile: &'static [u8],
}

fn eq_index(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |weight, (bit, value)| {
            weight
                * if (index >> bit) & 1 == 1 {
                    *value
                } else {
                    Fr::one() - value
                }
        })
}

fn endpoint_bit(endpoint: &[u8; 32], bit: usize) -> Fr {
    Fr::from(((endpoint[bit / 8] >> (bit % 8)) & 1) as u64)
}

fn parent_map(bytes: &[[usize; 8]], source_width: usize) -> Result<[usize; ID_BITS], String> {
    if source_width != header_hash::SERIALIZER_WIDTH || bytes.len() != 32 {
        return Err("canonical serializer parent map shape changed".into());
    }
    let mut result = [0; ID_BITS];
    for (byte, wires) in bytes.iter().enumerate() {
        for (bit, &source) in wires.iter().enumerate() {
            if source >= source_width {
                return Err("serializer parent source outside local input".into());
            }
            result[8 * byte + bit] = header_hash::SERIALIZER_OFFSET
                .checked_add(source)
                .filter(|wire| *wire < LOCAL_INPUT_WIDTH)
                .ok_or("serializer parent wire outside local input")?;
        }
    }
    Ok(result)
}

fn validate_maps(parent: &[usize; ID_BITS], digest: &[usize; ID_BITS]) -> Result<(), String> {
    let mut indices: Vec<usize> = Vec::with_capacity(ID_BITS * 2);
    indices.extend(parent);
    indices.extend(digest);
    if indices.iter().any(|&wire| wire >= LOCAL_INPUT_WIDTH) {
        return Err("canonical bit map outside local input".into());
    }
    indices.sort_unstable();
    if indices.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err("canonical parent and digest bit maps overlap".into());
    }
    Ok(())
}

impl HeaderAdjacencyLayout {
    /// Compile a bounded owner-slot descriptor from canonical serializer and
    /// digest maps. No history-sized circuit, witness, or gate list is built.
    pub fn compile(
        n: u64,
        slot_log: usize,
        start: [u8; 32],
        tip: [u8; 32],
    ) -> Result<Self, String> {
        Self::compile_owned_maps(n, slot_log, start, tip, PROFILE, || {
            let compiled = serializer::build(None)?;
            let parent_wires = parent_map(
                &compiled.layout.fields.parent_id,
                compiled.circuit.input_len,
            )?;
            let mut digest_wires = [0usize; ID_BITS];
            for (bit, wire) in digest_wires.iter_mut().enumerate() {
                *wire = segment_relation::DIGEST_OFFSET
                    .checked_add(bit)
                    .filter(|index| *index < LOCAL_INPUT_WIDTH)
                    .ok_or("digest wire outside local input")?;
            }
            Ok((parent_wires, digest_wires))
        })
    }

    /// Code-owned previous/current metadata maps with typed history endpoints.
    /// This relation needs the order circuit and serialized current-field aliases
    /// in the same commitment; it does not authenticate a header by itself.
    pub(crate) fn compile_metadata(n: u64, slot_log: usize, tip_time: i64) -> Result<Self, String> {
        let height = u32::try_from(n).map_err(|_| "metadata terminal height exceeds u32")?;
        let mut start = [0u8; 32];
        start[12] = 1;
        let mut tip = [0u8; 32];
        tip[..4].copy_from_slice(&height.to_le_bytes());
        tip[4..12].copy_from_slice(&tip_time.to_le_bytes());
        Self::compile_owned_maps(n, slot_log, start, tip, METADATA_PROFILE, || {
            Ok((
                std::array::from_fn(|bit| header_order::ORDER_OFFSET + bit),
                std::array::from_fn(|bit| header_order::ORDER_OFFSET + ID_BITS + bit),
            ))
        })
    }

    // Only the two canonical constructors above can supply maps. The map
    // factory runs after all external dimensions have been validated.
    fn compile_owned_maps(
        n: u64,
        slot_log: usize,
        start: [u8; 32],
        tip: [u8; 32],
        profile: &'static [u8],
        maps: impl FnOnce() -> Result<([usize; ID_BITS], [usize; ID_BITS]), String>,
    ) -> Result<Self, String> {
        if usize::BITS < 64 {
            return Err("header adjacency requires 64-bit platform indices".into());
        }
        if n == 0 {
            return Err("header adjacency requires at least one owner slot".into());
        }
        if n > i32::MAX as u64 {
            return Err("header adjacency owner count exceeds i32 bound".into());
        }
        if slot_log > MAX_SLOT_LOG {
            return Err("header adjacency slot logarithm exceeds profile".into());
        }
        let owner_domain = 1u64
            .checked_shl(u32::try_from(slot_log).map_err(|_| "slot logarithm conversion overflow")?)
            .ok_or("header adjacency owner domain overflow")?;
        if n > owner_domain {
            return Err("header adjacency owner count exceeds slot domain".into());
        }

        let input_log = LOCAL_INPUT_LOG
            .checked_add(slot_log)
            .ok_or("header adjacency input logarithm overflow")?;
        let row_log = LOCAL_ROW_LOG
            .checked_add(slot_log)
            .ok_or("header adjacency row logarithm overflow")?;
        let input_len = 1usize
            .checked_shl(
                u32::try_from(input_log).map_err(|_| "input logarithm conversion overflow")?,
            )
            .ok_or("header adjacency input domain overflow")?;
        let row_count = 1usize
            .checked_shl(u32::try_from(row_log).map_err(|_| "row logarithm conversion overflow")?)
            .ok_or("header adjacency row domain overflow")?;
        let owner_count = usize::try_from(n).map_err(|_| "owner count does not fit usize")?;
        let term_count = owner_count
            .checked_add(1)
            .and_then(|count| count.checked_mul(ID_BITS))
            .ok_or("header adjacency term count overflow")?;

        let (parent_wires, digest_wires) = maps()?;
        validate_maps(&parent_wires, &digest_wires)?;

        Ok(Self {
            n,
            slot_log,
            input_log,
            row_log,
            input_len,
            row_count,
            term_count,
            parent_wires,
            digest_wires,
            start,
            tip,
            profile,
        })
    }

    pub fn n(&self) -> u64 {
        self.n
    }

    pub fn slot_log(&self) -> usize {
        self.slot_log
    }

    pub fn input_log(&self) -> usize {
        self.input_log
    }

    pub fn row_log(&self) -> usize {
        self.row_log
    }

    pub fn input_len(&self) -> usize {
        self.input_len
    }

    pub fn row_count(&self) -> usize {
        self.row_count
    }

    pub fn term_count(&self) -> usize {
        self.term_count
    }

    /// Bind the full descriptor before challenges. `append_u64` encodes each
    /// integer as an explicit eight-byte little-endian value.
    pub fn bind(&self, transcript: &mut Transcript) {
        self.bind_with_identity(transcript, self.profile, VERSION);
    }

    // Private seam for isolated identity tests; production always uses bind.
    fn bind_with_identity(&self, transcript: &mut Transcript, profile: &[u8], version: u64) {
        transcript.append_bytes(b"historical-adjacency-profile", profile);
        transcript.append_u64(b"historical-adjacency-version", version);
        transcript.append_u64(b"historical-adjacency-owners", self.n);
        transcript.append_u64(b"historical-adjacency-slot-log", self.slot_log as u64);
        transcript.append_u64(b"historical-adjacency-input-log", self.input_log as u64);
        transcript.append_u64(b"historical-adjacency-row-log", self.row_log as u64);
        transcript.append_u64(
            b"historical-adjacency-local-input-log",
            LOCAL_INPUT_LOG as u64,
        );
        transcript.append_u64(b"historical-adjacency-local-row-log", LOCAL_ROW_LOG as u64);
        for (parent, digest) in self.parent_wires.iter().zip(&self.digest_wires) {
            transcript.append_u64(b"historical-adjacency-parent-wire", *parent as u64);
            transcript.append_u64(b"historical-adjacency-digest-wire", *digest as u64);
        }
        transcript.append_bytes(b"historical-adjacency-start", &self.start);
        transcript.append_bytes(b"historical-adjacency-tip", &self.tip);
    }

    /// Emit gates for exactly one owner slot. Every slot translation and its
    /// row/input bounds are checked before the first sink call. Sink failure
    /// may stop a valid emission partway through; the owning packet writer is
    /// responsible for discarding an incomplete packet in that case.
    pub fn visit_slot_terms(
        &self,
        slot: u64,
        mut sink: impl FnMut(usize, Gate) -> Result<(), String>,
    ) -> Result<usize, String> {
        if slot >= self.n {
            return Err("header adjacency slot outside owner history".into());
        }
        let slot = usize::try_from(slot).map_err(|_| "header adjacency slot does not fit usize")?;
        let local_input_width = LOCAL_INPUT_WIDTH;
        let row_base = slot
            .checked_mul(LOCAL_ROW_WIDTH)
            .ok_or("header adjacency owner row offset overflow")?;
        let row_last = row_base
            .checked_add(LOCAL_ROW_WIDTH - 1)
            .filter(|row| *row < self.row_count)
            .ok_or("header adjacency owner rows outside global domain")?;
        let input_base = slot
            .checked_mul(local_input_width)
            .ok_or("header adjacency owner input offset overflow")?;
        let input_last = input_base
            .checked_add(local_input_width - 1)
            .filter(|wire| *wire < self.input_len)
            .ok_or("header adjacency owner input outside global domain")?;
        let previous_base = if slot > 0 {
            let previous = slot - 1;
            let base = previous
                .checked_mul(local_input_width)
                .ok_or("header adjacency predecessor input offset overflow")?;
            base.checked_add(local_input_width - 1)
                .filter(|wire| *wire < self.input_len)
                .ok_or("header adjacency predecessor input outside global domain")?;
            Some(base)
        } else {
            None
        };
        // Explicitly establish each translated endpoint's bounds before the
        // callback can observe any term.
        for wire in self.parent_wires.iter().chain(&self.digest_wires) {
            input_base
                .checked_add(*wire)
                .filter(|translated| *translated <= input_last && *translated < self.input_len)
                .ok_or("header adjacency local wire translation outside global input")?;
            if let Some(base) = previous_base {
                base.checked_add(*wire)
                    .filter(|translated| *translated < self.input_len)
                    .ok_or("header adjacency predecessor wire translation outside global input")?;
            }
        }
        let last_row = if slot as u64 + 1 == self.n {
            row_base
                .checked_add(ID_BITS * 2 - 1)
                .filter(|row| *row <= row_last && *row < self.row_count)
                .ok_or("header adjacency terminal rows outside global domain")?
        } else {
            row_last
        };
        let _ = last_row;

        let zero = Fr::zero();
        let one = Fr::one();
        let mut emitted = 0usize;
        let mut emit = |row: usize, left: usize, right: usize, c0: Fr, c1: Fr, c2: Fr, c3: Fr| {
            sink(
                row,
                Gate {
                    left,
                    right,
                    c0,
                    c1,
                    c2,
                    c3,
                },
            )?;
            emitted = emitted
                .checked_add(1)
                .ok_or("header adjacency emitted count overflow")?;
            Ok::<(), String>(())
        };

        if slot == 0 {
            for bit in 0..ID_BITS {
                let row = row_base + bit;
                let left = input_base + self.parent_wires[bit];
                emit(
                    row,
                    left,
                    0,
                    -endpoint_bit(&self.start, bit),
                    one,
                    zero,
                    zero,
                )?;
            }
        }
        if let Some(previous_base) = previous_base {
            for bit in 0..ID_BITS {
                let row = row_base + bit;
                let left = previous_base + self.digest_wires[bit];
                let right = input_base + self.parent_wires[bit];
                emit(row, left, right, zero, one, -one, zero)?;
            }
        }
        if slot as u64 + 1 == self.n {
            for bit in 0..ID_BITS {
                let row = row_base + ID_BITS + bit;
                let left = input_base + self.digest_wires[bit];
                emit(row, left, 0, -endpoint_bit(&self.tip, bit), one, zero, zero)?;
            }
        }
        Ok(emitted)
    }

    /// Evaluate the exact gate sum in O(256 + h) field work and O(h) scratch
    /// space. No owner-slot enumeration or history-sized table is used.
    pub fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let expected_row = LOCAL_ROW_LOG
            .checked_add(self.slot_log)
            .ok_or("header adjacency row dimension overflow")?;
        let expected_input = LOCAL_INPUT_LOG
            .checked_add(self.slot_log)
            .ok_or("header adjacency input dimension overflow")?;
        if r.len() != expected_row || u.len() != expected_input || v.len() != expected_input {
            return Err("header adjacency coefficient point dimensions rejected".into());
        }
        let (r_local, r_owner) = r.split_at(LOCAL_ROW_LOG);
        let (u_local, u_owner) = u.split_at(LOCAL_INPUT_LOG);
        let (v_local, v_owner) = v.split_at(LOCAL_INPUT_LOG);
        let link_owner = wiring::evaluate_shift(
            r_owner,
            u_owner,
            v_owner,
            1,
            1,
            self.n,
            0,
            RightIndex::SameRow,
        )?;

        let mut link_local = Fr::zero();
        let mut first = [Fr::zero(); 2];
        let mut last = [Fr::zero(); 2];
        for bit in 0..ID_BITS {
            let row_weight = eq_index(r_local, bit);
            link_local += row_weight
                * eq_index(u_local, self.digest_wires[bit])
                * eq_index(v_local, self.parent_wires[bit]);

            let first_weight = row_weight * eq_index(u_local, self.parent_wires[bit]);
            first[0] -= first_weight * endpoint_bit(&self.start, bit);
            first[1] += first_weight;

            let last_weight =
                eq_index(r_local, ID_BITS + bit) * eq_index(u_local, self.digest_wires[bit]);
            last[0] -= last_weight * endpoint_bit(&self.tip, bit);
            last[1] += last_weight;
        }

        let right_global_zero = eq_index(v, 0);
        let first_owner = eq_index(r_owner, 0) * eq_index(u_owner, 0) * right_global_zero;
        let last_owner = eq_index(
            r_owner,
            usize::try_from(self.n - 1).map_err(|_| "last owner index overflow")?,
        ) * eq_index(
            u_owner,
            usize::try_from(self.n - 1).map_err(|_| "last owner index overflow")?,
        ) * right_global_zero;
        let link = link_local * link_owner;
        Ok([
            first[0] * first_owner + last[0] * last_owner,
            link + first[1] * first_owner + last[1] * last_owner,
            -link,
            Fr::zero(),
        ])
    }
}

#[cfg(test)]
pub(crate) mod linear_for_test {
    use super::*;

    // Private fields and constructors keep this a borrowed canonical descriptor,
    // rather than a numeric exception or caller-supplied map interface.
    pub(crate) struct Descriptor<'a> {
        native: Option<&'a HeaderAdjacencyLayout>,
        native_only: bool,
        active: usize, padded: usize, local_input: usize, local_row: usize,
        parent: &'a [usize], digest: &'a [usize], start: &'a [u8;32], tip: &'a [u8;32],
    }
    impl HeaderAdjacencyLayout {
        pub(crate) fn linear_descriptor_for_test(&self)->Result<Descriptor<'_>,String>{
            if !matches!(self.n,3|4)||self.slot_log!=2||self.input_log!=22||self.row_log!=11
                ||self.profile!=PROFILE||self.input_len!=1<<22||self.row_count!=1<<11
                ||self.term_count!=(self.n as usize+1)*256 {
                return Err("linear diagnostic requires canonical N3/N4 layout".into());
            }
            Ok(Descriptor{native:Some(self),native_only:false,active:self.n as usize,padded:4,local_input:20,local_row:9,
                parent:&self.parent_wires,digest:&self.digest_wires,start:&self.start,tip:&self.tip})
        }
        pub(crate) fn cache_eviction_descriptor_for_test(&self)->Result<Descriptor<'_>,String>{
            if self.n!=7||self.slot_log!=3||self.input_log!=23||self.row_log!=12
                ||self.profile!=PROFILE||self.input_len!=1<<23||self.row_count!=1<<12
                ||self.term_count!=2048 {
                return Err("cache-eviction diagnostic requires canonical N7/eight-owner layout".into());
            }
            Ok(Descriptor{native:Some(self),native_only:false,active:7,padded:8,local_input:20,local_row:9,
                parent:&self.parent_wires,digest:&self.digest_wires,start:&self.start,tip:&self.tip})
        }
        pub(crate) fn historical_h3_descriptor_for_test(&self)->Result<Descriptor<'_>,String>{
            if !matches!(self.n,5|8)||self.slot_log!=3||self.input_log!=23||self.row_log!=12
                ||self.profile!=PROFILE||self.input_len!=1<<23||self.row_count!=1<<12
                ||self.term_count!=(self.n as usize+1)*256 {
                return Err("scaling41 adjacency canonical H3 layout".into());
            }
            Ok(Descriptor{native:Some(self),native_only:false,active:self.n as usize,padded:8,local_input:20,local_row:9,
                parent:&self.parent_wires,digest:&self.digest_wires,start:&self.start,tip:&self.tip})
        }
        /// Separate diagnostic descriptor; it cannot enter the generic,
        /// Native32 or Historical50 admission paths.
        pub(crate) fn h21_role5_descriptor_for_test(&self)->Result<Descriptor<'_>,String>{
            let d=Descriptor {native:Some(self),native_only:true,active:crate::h21_snapshot::N,padded:1<<21,
                local_input:20,local_row:9,parent:&self.parent_wires,digest:&self.digest_wires,
                start:&self.start,tip:&self.tip};
            d.validate_h21(1usize<<41)?;Ok(d)
        }
        pub(crate) fn native_role5_descriptor_for_test(&self,
            admission:&crate::native_prefix_auth_plan::NativeRole5Admission<'_, '_>)
            ->Result<Descriptor<'_>,String>{
            admission.require_layout(self)?;
            if self.n!=3073||self.slot_log!=12||self.input_log!=32||self.row_log!=21
                ||self.profile!=PROFILE||self.input_len!=1usize<<32||self.row_count!=1usize<<21
                ||self.term_count!=786944{return Err("native role5 canonical descriptor geometry".into());}
            Ok(Descriptor{native:Some(self),native_only:true,active:3073,padded:4096,local_input:20,local_row:9,
                parent:&self.parent_wires,digest:&self.digest_wires,start:&self.start,tip:&self.tip})
        }
        pub(crate) fn historical50_role5_descriptor_for_test(&self,
            admission:&crate::historical_prefix_proof::Historical50Role5Admission<'_, '_>)
            ->Result<Descriptor<'_>,String>{
            admission.require_layout(self)?;
            if self.n!=3073||self.slot_log!=12||self.input_log!=32||self.row_log!=21||self.profile!=PROFILE
                ||self.input_len!=1usize<<32||self.row_count!=1usize<<21||self.term_count!=786944{
                return Err("historical50 role5 descriptor geometry".into());}
            Ok(Descriptor{native:Some(self),native_only:true,active:3073,padded:4096,local_input:20,local_row:9,
                parent:&self.parent_wires,digest:&self.digest_wires,start:&self.start,tip:&self.tip})
        }
    }
    impl Descriptor<'static> {
        pub(crate) fn owner_toy()->Self{
            const PARENT:[usize;1]=[1];const DIGEST:[usize;1]=[0];const ZERO:[u8;32]=[0;32];
            Self{native:None,native_only:false,active:3073,padded:4096,local_input:1,local_row:1,
                parent:&PARENT,digest:&DIGEST,start:&ZERO,tip:&ZERO}
        }
    }
    impl Descriptor<'_> {
        pub(crate) fn active(&self)->usize{self.active}
        pub(crate) fn padded(&self)->usize{self.padded}
        pub(crate) fn local_input(&self)->usize{self.local_input}
        pub(crate) fn local_row(&self)->usize{self.local_row}
        pub(crate) fn ids(&self)->usize{self.parent.len()}
        pub(crate) fn parent(&self)->&[usize]{self.parent}
        pub(crate) fn digest(&self)->&[usize]{self.digest}
        pub(crate) fn start_bit(&self,j:usize)->Fr{endpoint_bit(self.start,j)}
        pub(crate) fn tip_bit(&self,j:usize)->Fr{endpoint_bit(self.tip,j)}
        pub(crate) fn owner_bits(&self)->usize{self.padded.trailing_zeros() as usize}
        pub(crate) fn input_log(&self)->usize{self.local_input+self.owner_bits()}
        pub(crate) fn row_log(&self)->usize{self.local_row+self.owner_bits()}
        pub(crate) fn input_len(&self)->usize{1usize<<self.input_log()}
        pub(crate) fn row_count(&self)->usize{1usize<<self.row_log()}
        pub(crate) fn chunk_bits(&self)->usize{if self.native.is_some(){16}else{1}}
        pub(crate) fn validate(&self,source_len:usize,chunk_bits:usize)->Result<(),String>{
            if self.native_only{return Err("native32 descriptor requires computed role5 capability".into());}
            let geometry=(self.active,self.padded,self.local_input,self.local_row,self.ids(),chunk_bits);
            let allowed=match self.native {
                Some(layout)=>((matches!(geometry,(3|4,4,20,9,256,16))&&layout.slot_log==2)
                    ||(geometry==(7,8,20,9,256,16)&&layout.slot_log==3)
                    ||(matches!(geometry,(5|8,8,20,9,256,16))&&layout.slot_log==3
                        &&layout.input_log==23&&layout.row_log==12&&layout.input_len==1<<23&&layout.row_count==1<<12
                        &&layout.term_count==(self.active+1)*256))&&layout.profile==PROFILE
                    &&layout.n as usize==self.active,
                None=>geometry==(3073,4096,1,1,1,1)&&self.parent==[1]&&self.digest==[0],
            };
            if !allowed||source_len!=self.input_len()||self.digest.len()!=self.ids(){
                return Err("linear diagnostic geometry/source rejected before activity".into());
            }
            Ok(())
        }
        pub(crate) fn validate_h21(&self,source_len:usize)->Result<(),String>{
            let layout=self.native.ok_or("H21 role5 descriptor has no canonical layout")?;
            if usize::BITS!=64 || !self.native_only
                ||(self.active,self.padded,self.local_input,self.local_row,self.ids(),self.chunk_bits())
                    !=(crate::h21_snapshot::N,1<<21,20,9,256,16)
                ||source_len!=1usize<<41 ||self.input_log()!=41||self.row_log()!=30
                ||layout.profile!=PROFILE||layout.n!=crate::h21_snapshot::N as u64||layout.slot_log!=21
                ||layout.input_log!=41||layout.row_log!=30||layout.input_len!=1usize<<41
                ||layout.row_count!=1usize<<30||layout.term_count!=(crate::h21_snapshot::N+1)*256
                ||self.start!=&[0;32]||self.start!=&layout.start||self.tip!=&layout.tip
                ||self.parent!=layout.parent_wires||self.digest!=layout.digest_wires {
                return Err("H21 role5 canonical descriptor geometry/maps/endpoints".into());
            }
            validate_maps(&layout.parent_wires,&layout.digest_wires)
        }
        pub(crate) fn require_h21_layout(&self,layout:&HeaderAdjacencyLayout)->Result<(),String>{
            self.validate_h21(1usize<<41)?;
            if !self.native.is_some_and(|expected|std::ptr::eq(expected,layout)) {
                return Err("H21 role5 detached canonical layout".into());
            }
            Ok(())
        }
        pub(crate) fn validate_native(&self,
            admission:&crate::native_prefix_auth_plan::NativeRole5Admission<'_, '_>)->Result<(),String>{
            let layout=self.native.ok_or("native role5 descriptor has no layout")?;
            if !self.native_only||(self.active,self.padded,self.local_input,self.local_row,self.ids(),self.chunk_bits())
                !=(3073,4096,20,9,256,16)||self.digest.len()!=256||layout.profile!=PROFILE
                ||layout.n!=3073||layout.slot_log!=12||layout.input_log!=32||layout.row_log!=21
                ||layout.term_count!=786944{return Err("native role5 descriptor policy/geometry".into());}
            admission.require_layout(layout)
        }
        pub(crate) fn validate_historical50(&self,
            admission:&crate::historical_prefix_proof::Historical50Role5Admission<'_, '_>)->Result<(),String>{
            let layout=self.native.ok_or("historical50 role5 descriptor layout")?;
            if !self.native_only||(self.active,self.padded,self.local_input,self.local_row,self.ids(),self.chunk_bits())
                !=(3073,4096,20,9,256,16)||self.digest.len()!=256||layout.profile!=PROFILE
                ||layout.n!=3073||layout.slot_log!=12||layout.input_log!=32||layout.row_log!=21
                ||layout.term_count!=786944{return Err("historical50 role5 descriptor policy".into());}
            admission.require_layout(layout)
        }
        pub(crate) fn bind(&self,t:&mut Transcript){
            if let Some(layout)=self.native{return layout.bind(t);}
            // Closed one-bit projection, using the existing descriptor framing.
            t.append_bytes(b"historical-adjacency-profile",PROFILE);
            t.append_u64(b"historical-adjacency-version",VERSION);
            for (label,value) in [(b"historical-adjacency-owners".as_slice(),self.active),
                (b"historical-adjacency-slot-log",self.owner_bits()),
                (b"historical-adjacency-input-log",self.input_log()),
                (b"historical-adjacency-row-log",self.row_log()),
                (b"historical-adjacency-local-input-log",self.local_input),
                (b"historical-adjacency-local-row-log",self.local_row)]{t.append_u64(label,value as u64);}
            for (parent,digest) in self.parent.iter().zip(self.digest){
                t.append_u64(b"historical-adjacency-parent-wire",*parent as u64);
                t.append_u64(b"historical-adjacency-digest-wire",*digest as u64);
            }
            t.append_bytes(b"historical-adjacency-start",self.start);t.append_bytes(b"historical-adjacency-tip",self.tip);
        }
        pub(crate) fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
            if let Some(layout)=self.native{return layout.coefficients(r,u,v);}
            if r.len()!=13||u.len()!=13||v.len()!=13{return Err("toy linear coefficient dimensions".into());}
            let link=wiring::evaluate_shift(&r[1..],&u[1..],&v[1..],1,1,3073,0,RightIndex::SameRow)?
                *eq_index(&r[..1],0)*eq_index(&u[..1],0)*eq_index(&v[..1],1);
            let zero=eq_index(v,0);
            let first=eq_index(&r[..1],0)*eq_index(&r[1..],0)*eq_index(&u[..1],1)*eq_index(&u[1..],0)*zero;
            let last=eq_index(&r[..1],1)*eq_index(&r[1..],3072)*eq_index(&u[..1],0)*eq_index(&u[1..],3072)*zero;
            Ok([Fr::zero(),link+first+last,-link,Fr::zero()])
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn native32_descriptor_cannot_enter_callback_producer_or_preflight(){
            let layout=HeaderAdjacencyLayout::compile(3073,12,[0;32],[0;32]).unwrap();
            assert!(layout.linear_descriptor_for_test().is_err());
            assert!(layout.cache_eviction_descriptor_for_test().is_err());
            // Module-local construction tests the refusal boundary; it cannot
            // mint a NativeRole5Admission or enter the sealed native producer.
            let d=Descriptor{native:Some(&layout),native_only:true,active:3073,padded:4096,
                local_input:20,local_row:9,parent:&layout.parent_wires,digest:&layout.digest_wires,
                start:&layout.start,tip:&layout.tip};
            assert!(d.validate(1usize<<32,16).is_err());
            assert!(crate::segment_adjacency::linear_for_test::preflight_for_test(&d,0).is_err());
            let calls=std::cell::Cell::new(0);let mut t=Transcript::new(b"native-descriptor-callback-refusal");
            t.append_bytes(b"retained-prefix",b"unchanged");
            let before=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
            let continuation=t.clone().challenge_scalar(b"continuation");
            assert!(crate::segment_adjacency::linear_for_test::prove(&d,1usize<<32,0,
                |_|{calls.set(calls.get()+1);Err("must not load".into())},&mut t).is_err());
            assert_eq!(calls.get(),0);assert_eq!([t.challenges(),t.raw_queries(),t.bytes_absorbed()],before);
            assert_eq!(t.clone().challenge_scalar(b"continuation"),continuation);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::segment_adjacency;

    fn endpoint(seed: u8) -> [u8; 32] {
        std::array::from_fn(|i| seed.wrapping_add((i as u8).wrapping_mul(29)))
    }

    fn point(width: usize, seed: u64) -> Vec<Fr> {
        (0..width)
            .map(|i| Fr::from(seed + 2 + i as u64 * 17))
            .collect()
    }

    fn boolean_point(index: usize, width: usize) -> Vec<Fr> {
        (0..width)
            .map(|bit| Fr::from(((index >> bit) & 1) as u64))
            .collect()
    }

    fn direct_eq(point: &[Fr], index: usize) -> Fr {
        let mut value = Fr::one();
        for bit in 0..point.len() {
            value *= if (index >> bit) & 1 == 1 {
                point[bit]
            } else {
                Fr::one() - point[bit]
            };
        }
        value
    }

    /// Test-only oracle: derive canonical maps and integer owner/row/wire
    /// coordinates directly. It never calls the new emitter, coefficients, or
    /// the shift kernel.
    fn reference_gates(n: u64, start: &[u8; 32], tip: &[u8; 32]) -> Vec<(usize, Gate)> {
        let compiled = serializer::build(None).unwrap();
        let parents: [usize; ID_BITS] = std::array::from_fn(|bit| {
            header_hash::SERIALIZER_OFFSET + compiled.layout.fields.parent_id[bit / 8][bit % 8]
        });
        let digests: [usize; ID_BITS] =
            std::array::from_fn(|bit| segment_relation::DIGEST_OFFSET + bit);
        let mut gates = Vec::with_capacity((n as usize + 1) * ID_BITS);
        for owner in 0..n {
            let owner = owner as usize;
            let row_base = owner * LOCAL_ROW_WIDTH;
            let input_base = owner * LOCAL_INPUT_WIDTH;
            if owner == 0 {
                for bit in 0..ID_BITS {
                    gates.push((
                        row_base + bit,
                        Gate {
                            left: input_base + parents[bit],
                            right: 0,
                            c0: -Fr::from(((start[bit / 8] >> (bit % 8)) & 1) as u64),
                            c1: Fr::one(),
                            c2: Fr::zero(),
                            c3: Fr::zero(),
                        },
                    ));
                }
            }
            if owner > 0 {
                let previous_input = (owner - 1) * LOCAL_INPUT_WIDTH;
                for bit in 0..ID_BITS {
                    gates.push((
                        row_base + bit,
                        Gate {
                            left: previous_input + digests[bit],
                            right: input_base + parents[bit],
                            c0: Fr::zero(),
                            c1: Fr::one(),
                            c2: -Fr::one(),
                            c3: Fr::zero(),
                        },
                    ));
                }
            }
            if owner + 1 == n as usize {
                for bit in 0..ID_BITS {
                    gates.push((
                        row_base + ID_BITS + bit,
                        Gate {
                            left: input_base + digests[bit],
                            right: 0,
                            c0: -Fr::from(((tip[bit / 8] >> (bit % 8)) & 1) as u64),
                            c1: Fr::one(),
                            c2: Fr::zero(),
                            c3: Fr::zero(),
                        },
                    ));
                }
            }
        }
        gates
    }

    fn direct_coefficients(gates: &[(usize, Gate)], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
        let mut result = [Fr::zero(); 4];
        for (row, gate) in gates {
            let weight = direct_eq(r, *row) * direct_eq(u, gate.left) * direct_eq(v, gate.right);
            result[0] += weight * gate.c0;
            result[1] += weight * gate.c1;
            result[2] += weight * gate.c2;
            result[3] += weight * gate.c3;
        }
        result
    }

    fn bound_challenge(layout: &HeaderAdjacencyLayout) -> Fr {
        let mut transcript = Transcript::new(b"header-adjacency-binding-test");
        layout.bind(&mut transcript);
        transcript.challenge_scalar(b"first-bound-challenge")
    }

    #[test]
    fn n3_last_link_and_padding_independent_oracle() {
        let (start, tip) = (endpoint(7), endpoint(91));
        let layout = HeaderAdjacencyLayout::compile(3, 2, start, tip).unwrap();
        assert_eq!(layout.input_log(), 22);
        assert_eq!(layout.row_log(), 11);
        assert_eq!(layout.term_count(), 1024);
        let reference = reference_gates(3, &start, &tip);
        assert_eq!(reference.len(), layout.term_count());

        let compiled = serializer::build(None).unwrap();
        let parents: [usize; ID_BITS] = std::array::from_fn(|bit| {
            header_hash::SERIALIZER_OFFSET + compiled.layout.fields.parent_id[bit / 8][bit % 8]
        });
        let digests: [usize; ID_BITS] =
            std::array::from_fn(|bit| segment_relation::DIGEST_OFFSET + bit);

        // The last active internal edge (owner 2) must use child row 2, the
        // previous digest bank 1, and the parent bank 2.
        let selected_bit = 173usize;
        let mut emitted = Vec::new();
        let emitted_count = layout
            .visit_slot_terms(2, |row, gate| {
                emitted.push((row, gate));
                Ok(())
            })
            .unwrap();
        assert_eq!(emitted_count, 512);
        assert_eq!(emitted.len(), 512);
        for (row, gate) in &emitted {
            assert!(reference.contains(&(*row, gate.clone())));
        }
        let row_index = (2 << LOCAL_ROW_LOG) + selected_bit;
        let left_index = (1 << LOCAL_INPUT_LOG) + digests[selected_bit];
        let right_index = (2 << LOCAL_INPUT_LOG) + parents[selected_bit];
        let r = boolean_point(row_index, LOCAL_ROW_LOG + 2);
        let u = boolean_point(left_index, LOCAL_INPUT_LOG + 2);
        let v = boolean_point(right_index, LOCAL_INPUT_LOG + 2);
        assert_eq!(
            layout.coefficients(&r, &u, &v).unwrap(),
            [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
        );
        assert_eq!(
            direct_coefficients(&reference, &r, &u, &v),
            [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
        );

        // Owner 3 is padding for N=3. Even selecting that owner and the last
        // active input bank contributes no link or terminal anchor.
        let padded_r = boolean_point((3 << LOCAL_ROW_LOG) + selected_bit, LOCAL_ROW_LOG + 2);
        let padded_u = boolean_point(left_index, LOCAL_INPUT_LOG + 2);
        let padded_v = boolean_point(
            (3 << LOCAL_INPUT_LOG) + parents[selected_bit],
            LOCAL_INPUT_LOG + 2,
        );
        assert_eq!(
            layout
                .coefficients(&padded_r, &padded_u, &padded_v)
                .unwrap(),
            [Fr::zero(); 4]
        );
        assert_eq!(
            direct_coefficients(&reference, &padded_r, &padded_u, &padded_v),
            [Fr::zero(); 4]
        );

        let (r, u, v) = (
            point(LOCAL_ROW_LOG + 2, 13),
            point(LOCAL_INPUT_LOG + 2, 37),
            point(LOCAL_INPUT_LOG + 2, 101),
        );
        assert_eq!(
            layout.coefficients(&r, &u, &v).unwrap(),
            direct_coefficients(&reference, &r, &u, &v)
        );
        let mut all_emitted = Vec::new();
        for slot in 0..3 {
            layout
                .visit_slot_terms(slot, |row, gate| {
                    all_emitted.push((row, gate));
                    Ok(())
                })
                .unwrap();
        }
        all_emitted.sort_by_key(|term| term.0);
        let mut reference_sorted = reference.clone();
        reference_sorted.sort_by_key(|term| term.0);
        assert_eq!(all_emitted, reference_sorted);
    }

    #[test]
    fn n1_2_4_match_legacy_coefficients_without_changing_legacy_admission() {
        let (start, tip) = (endpoint(11), endpoint(42));
        let compiled = serializer::build(None).unwrap();
        let parents = std::array::from_fn(|bit| {
            header_hash::SERIALIZER_OFFSET + compiled.layout.fields.parent_id[bit / 8][bit % 8]
        });
        let digests = std::array::from_fn(|bit| segment_relation::DIGEST_OFFSET + bit);
        for n in [1u64, 2, 4] {
            let h = n.trailing_zeros() as usize;
            let layout = HeaderAdjacencyLayout::compile(n, h, start, tip).unwrap();
            let old =
                segment_adjacency::Relation::new(n as usize, parents, digests, start, tip).unwrap();
            for seed in [3, 29, 107] {
                let (r, u, v) = (
                    point(LOCAL_ROW_LOG + h, seed),
                    point(LOCAL_INPUT_LOG + h, seed + 19),
                    point(LOCAL_INPUT_LOG + h, seed + 83),
                );
                assert_eq!(
                    layout.coefficients(&r, &u, &v).unwrap(),
                    old.wiring_coefficients(&r, &u, &v).unwrap()
                );
            }
        }
        assert!(segment_adjacency::Relation::new(8, parents, digests, start, tip).is_err());
    }

    #[test]
    fn validation_and_prevalidation_fail_before_sink() {
        let start = endpoint(1);
        let tip = endpoint(2);
        assert!(HeaderAdjacencyLayout::compile(0, 0, start, tip).is_err());
        assert!(HeaderAdjacencyLayout::compile(1, 22, start, tip).is_err());
        assert!(HeaderAdjacencyLayout::compile(5, 2, start, tip).is_err());
        assert!(HeaderAdjacencyLayout::compile(i32::MAX as u64 + 1, 21, start, tip).is_err());
        assert!(HeaderAdjacencyLayout::compile(1, 21, start, tip).is_ok());
        let one = HeaderAdjacencyLayout::compile(1, 0, start, tip).unwrap();
        assert_eq!(
            (one.input_log(), one.row_log(), one.term_count()),
            (20, 9, 512)
        );
        let mut calls = 0usize;
        assert!(one
            .visit_slot_terms(1, |_, _| {
                calls += 1;
                Ok(())
            })
            .is_err());
        assert_eq!(calls, 0);
        for bad in [
            {
                let mut p = one.clone();
                p.input_len = LOCAL_INPUT_WIDTH - 1;
                p
            },
            {
                let mut p = one.clone();
                p.row_count = LOCAL_ROW_WIDTH - 1;
                p
            },
            {
                let mut p = one.clone();
                p.digest_wires[0] = LOCAL_INPUT_WIDTH;
                p
            },
        ] {
            let mut calls = 0;
            assert!(bad
                .visit_slot_terms(0, |_, _| {
                    calls += 1;
                    Ok(())
                })
                .is_err());
            assert_eq!(calls, 0);
        }

        let n3 = HeaderAdjacencyLayout::compile(3, 2, start, tip).unwrap();
        for (r, u, v) in [
            (
                vec![Fr::zero(); 10],
                vec![Fr::zero(); 22],
                vec![Fr::zero(); 22],
            ),
            (
                vec![Fr::zero(); 11],
                vec![Fr::zero(); 21],
                vec![Fr::zero(); 22],
            ),
            (
                vec![Fr::zero(); 11],
                vec![Fr::zero(); 22],
                vec![Fr::zero(); 23],
            ),
        ] {
            assert!(n3.coefficients(&r, &u, &v).is_err());
        }
        // Each point independently rejects both a missing and an extra bit.
        for axis in 0..3 {
            for extra in [false, true] {
                let mut points = [
                    vec![Fr::zero(); 11],
                    vec![Fr::zero(); 22],
                    vec![Fr::zero(); 22],
                ];
                if extra {
                    points[axis].push(Fr::zero());
                } else {
                    points[axis].pop();
                }
                assert_eq!(
                    n3.coefficients(&points[0], &points[1], &points[2])
                        .unwrap_err(),
                    "header adjacency coefficient point dimensions rejected"
                );
            }
        }
    }

    #[test]
    fn canonical_map_guards_reject_isolated_faults() {
        let compiled = serializer::build(None).unwrap();
        let bytes = compiled.layout.fields.parent_id;
        let parents = parent_map(&bytes, header_hash::SERIALIZER_WIDTH).unwrap();
        let digests = std::array::from_fn(|bit| segment_relation::DIGEST_OFFSET + bit);
        validate_maps(&parents, &digests).unwrap();
        assert_eq!(
            parent_map(&bytes[..31], header_hash::SERIALIZER_WIDTH).unwrap_err(),
            "canonical serializer parent map shape changed"
        );
        assert_eq!(
            parent_map(&bytes, header_hash::SERIALIZER_WIDTH - 1).unwrap_err(),
            "canonical serializer parent map shape changed"
        );
        let mut outside = bytes;
        outside[0][0] = header_hash::SERIALIZER_WIDTH;
        assert_eq!(
            parent_map(&outside, header_hash::SERIALIZER_WIDTH).unwrap_err(),
            "serializer parent source outside local input"
        );
        for is_parent in [true, false] {
            let (mut p, mut d) = (parents, digests);
            if is_parent {
                p[0] = LOCAL_INPUT_WIDTH;
            } else {
                d[0] = LOCAL_INPUT_WIDTH;
            }
            assert_eq!(
                validate_maps(&p, &d).unwrap_err(),
                "canonical bit map outside local input"
            );
            let (mut p, mut d) = (parents, digests);
            if is_parent {
                p[0] = p[1];
            } else {
                d[0] = d[1];
            }
            assert_eq!(
                validate_maps(&p, &d).unwrap_err(),
                "canonical parent and digest bit maps overlap"
            );
        }
        let mut cross = parents;
        cross[0] = digests[0];
        assert_eq!(
            validate_maps(&cross, &digests).unwrap_err(),
            "canonical parent and digest bit maps overlap"
        );
    }

    #[test]
    fn n5_partial_carry_and_isolated_relation_mutants() {
        let (start, tip) = (endpoint(17), endpoint(211));
        let layout = HeaderAdjacencyLayout::compile(5, 3, start, tip).unwrap();
        let reference = reference_gates(5, &start, &tip);
        let mut emitted = Vec::new();
        for slot in 0..5 {
            layout
                .visit_slot_terms(slot, |row, gate| {
                    emitted.push((row, gate));
                    Ok(())
                })
                .unwrap();
        }
        assert_eq!(emitted, reference);
        let (r, u, v) = (point(12, 5), point(23, 37), point(23, 137));
        let expected = direct_coefficients(&reference, &r, &u, &v);
        assert_ne!(
            expected,
            [Fr::zero(); 4],
            "mutant oracle must exercise the relation"
        );
        assert_eq!(layout.coefficients(&r, &u, &v).unwrap(), expected);
        let (mut mixed_r, mut mixed_u, mut mixed_v) = (r.clone(), u.clone(), v.clone());
        mixed_r[0] = Fr::zero();
        mixed_u[1] = Fr::one();
        mixed_v[2] = Fr::zero();
        assert_eq!(
            layout.coefficients(&mixed_r, &mixed_u, &mixed_v).unwrap(),
            direct_coefficients(&reference, &mixed_r, &mixed_u, &mixed_v)
        );
        let bit = 173;
        let last_link = 4 * LOCAL_ROW_WIDTH + bit;
        let position = reference
            .iter()
            .position(|(row, _)| *row == last_link)
            .unwrap();
        let selected = &reference[position].1;
        let points = (
            boolean_point(last_link, 12),
            boolean_point(selected.left, 23),
            boolean_point(selected.right, 23),
        );
        assert_eq!(
            layout
                .coefficients(&points.0, &points.1, &points.2)
                .unwrap(),
            [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
        );
        // Each mutant changes one row/edge or one endpoint bit, leaving others intact.
        for fault in 0..7 {
            let mut mutant = reference.clone();
            match fault {
                0 => {
                    mutant.remove(position);
                } // truncated upper link interval
                1 => {
                    let g = &mut mutant[position].1;
                    std::mem::swap(&mut g.left, &mut g.right);
                }
                2 => {
                    mutant[position].0 -= LOCAL_ROW_WIDTH;
                } // wrong owner row
                3 => {
                    mutant[position].1.right = 0;
                } // GlobalZero on an internal link
                4 => {
                    // terminal right must be global zero, not last-owner local zero
                    mutant.last_mut().unwrap().1.right = 4 * LOCAL_INPUT_WIDTH;
                }
                5 => {
                    mutant[0].1.c0 += Fr::one();
                }
                6 => {
                    mutant.last_mut().unwrap().1.c0 += Fr::one();
                }
                _ => unreachable!(),
            }
            assert_ne!(
                direct_coefficients(&mutant, &r, &u, &v),
                expected,
                "fault {fault}"
            );
        }
        let mut padding = reference.clone();
        let mut fake = selected.clone();
        fake.left += LOCAL_INPUT_WIDTH;
        fake.right += LOCAL_INPUT_WIDTH;
        padding.push((5 * LOCAL_ROW_WIDTH + bit, fake));
        assert_ne!(direct_coefficients(&padding, &r, &u, &v), expected);
        let mut one_start = start;
        one_start[0] ^= 1;
        let changed = HeaderAdjacencyLayout::compile(5, 3, one_start, tip).unwrap();
        assert_ne!(changed.coefficients(&r, &u, &v).unwrap(), expected);
        let mut one_tip = tip;
        one_tip[31] ^= 0x80;
        let changed = HeaderAdjacencyLayout::compile(5, 3, start, one_tip).unwrap();
        assert_ne!(changed.coefficients(&r, &u, &v).unwrap(), expected);
        // N=1 has both anchors and no internal link, on exact global-right-zero.
        let one = HeaderAdjacencyLayout::compile(1, 0, start, tip).unwrap();
        let one_ref = reference_gates(1, &start, &tip);
        for index in [0, 511] {
            let (row, gate) = &one_ref[index];
            let (r, u, v) = (
                boolean_point(*row, 9),
                boolean_point(gate.left, 20),
                boolean_point(0, 20),
            );
            assert_eq!(
                one.coefficients(&r, &u, &v).unwrap(),
                direct_coefficients(&one_ref, &r, &u, &v)
            );
        }
    }

    #[test]
    fn transcript_binding_covers_domain_maps_and_endpoints() {
        let (start, tip) = (endpoint(3), endpoint(70));
        let base = HeaderAdjacencyLayout::compile(3, 2, start, tip).unwrap();
        let baseline = bound_challenge(&base);
        let changed_n = HeaderAdjacencyLayout::compile(2, 2, start, tip).unwrap();
        let changed_h = HeaderAdjacencyLayout::compile(3, 3, start, tip).unwrap();
        let mut changed_start_bytes = start;
        changed_start_bytes[0] ^= 1;
        let changed_start = HeaderAdjacencyLayout::compile(3, 2, changed_start_bytes, tip).unwrap();
        let mut changed_tip_bytes = tip;
        changed_tip_bytes[31] ^= 1;
        let changed_tip = HeaderAdjacencyLayout::compile(3, 2, start, changed_tip_bytes).unwrap();
        let mut changed_maps = base.clone();
        changed_maps.parent_wires[0] ^= 1;
        for changed in [
            bound_challenge(&changed_n),
            bound_challenge(&changed_h),
            bound_challenge(&changed_start),
            bound_challenge(&changed_tip),
            bound_challenge(&changed_maps),
        ] {
            assert_ne!(baseline, changed);
        }
        assert_eq!(bound_challenge(&base), baseline);
        let mut digest_map = base.clone();
        digest_map.digest_wires.swap(0, 1);
        assert_ne!(bound_challenge(&digest_map), baseline);
        for input_dimension in [true, false] {
            let mut changed = base.clone();
            if input_dimension {
                changed.input_log += 1;
            } else {
                changed.row_log += 1;
            }
            assert_ne!(bound_challenge(&changed), baseline);
        }
        for (profile, version) in [
            (b"distinct-profile".as_slice(), VERSION),
            (PROFILE, VERSION + 1),
        ] {
            let mut t = Transcript::new(b"header-adjacency-binding-test");
            base.bind_with_identity(&mut t, profile, version);
            assert_ne!(t.challenge_scalar(b"first-bound-challenge"), baseline);
        }
        let mut context = Transcript::new(b"distinct-consumer-context");
        base.bind(&mut context);
        assert_ne!(context.challenge_scalar(b"first-bound-challenge"), baseline);

        let mut legacy = Transcript::new(b"header-adjacency-binding-test");
        segment_adjacency::Relation::new(
            1,
            std::array::from_fn(|i| i),
            std::array::from_fn(|i| 256 + i),
            start,
            tip,
        )
        .unwrap()
        .bind(&mut legacy);
        let legacy_challenge = legacy.challenge_scalar(b"first-bound-challenge");
        assert_ne!(baseline, legacy_challenge);
    }

    #[test]
    fn h21_stays_symbolic_and_dimension_bounded() {
        let layout =
            HeaderAdjacencyLayout::compile(1u64 << 21, 21, endpoint(5), endpoint(6)).unwrap();
        assert_eq!(layout.input_log(), 41);
        assert_eq!(layout.row_log(), 30);
        assert_eq!(layout.input_len(), 1usize << 41);
        assert_eq!(layout.row_count(), 1usize << 30);
        assert_eq!(layout.term_count(), 256 * ((1usize << 21) + 1));
        let (r, u, v) = (point(30, 7), point(41, 19), point(41, 43));
        assert!(layout.coefficients(&r, &u, &v).is_ok());
        let last = (1usize << 21) - 1;
        let r = boolean_point(last * LOCAL_ROW_WIDTH + 173, 30);
        let u = boolean_point(
            (last - 1) * LOCAL_INPUT_WIDTH + layout.digest_wires[173],
            41,
        );
        let v = boolean_point(last * LOCAL_INPUT_WIDTH + layout.parent_wires[173], 41);
        assert_eq!(
            layout.coefficients(&r, &u, &v).unwrap(),
            [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
        );
        let r = boolean_point(last * LOCAL_ROW_WIDTH + 256, 30);
        let u = boolean_point(last * LOCAL_INPUT_WIDTH + layout.digest_wires[0], 41);
        let v = boolean_point(0, 41);
        assert_eq!(
            layout.coefficients(&r, &u, &v).unwrap(),
            [-Fr::from(6u64 & 1), Fr::one(), Fr::zero(), Fr::zero()]
        );
        let partial =
            HeaderAdjacencyLayout::compile(last as u64, 21, endpoint(5), endpoint(6)).unwrap();
        assert_eq!(partial.coefficients(&r, &u, &v).unwrap(), [Fr::zero(); 4]);
    }

    #[test]
    fn metadata_owned_maps_typed_endpoints_and_binding_faults() {
        let layout = HeaderAdjacencyLayout::compile_metadata(3, 2, -17).unwrap();
        assert_eq!(layout.parent_wires, std::array::from_fn(|j| 794_624 + j));
        assert_eq!(layout.digest_wires, std::array::from_fn(|j| 794_880 + j));
        let mut first = [0u8; 32];
        first[12] = 1;
        let mut last = [0u8; 32];
        last[..4].copy_from_slice(&3u32.to_le_bytes());
        last[4..12].copy_from_slice(&(-17i64).to_le_bytes());
        assert_eq!(layout.start, first);
        assert_eq!(layout.tip, last);
        assert_eq!(layout.profile, METADATA_PROFILE);
        let baseline = bound_challenge(&layout);
        assert_eq!(
            bound_challenge(&HeaderAdjacencyLayout::compile_metadata(3, 2, -17).unwrap()),
            baseline
        );
        for variant in [
            HeaderAdjacencyLayout::compile_metadata(2, 2, -17).unwrap(),
            HeaderAdjacencyLayout::compile_metadata(3, 3, -17).unwrap(),
            HeaderAdjacencyLayout::compile_metadata(3, 2, 17).unwrap(),
        ] {
            assert_ne!(bound_challenge(&variant), baseline);
        }
        for map in 0..2 {
            for index in 0..ID_BITS {
                let mut fault = layout.clone();
                if map == 0 {
                    fault.parent_wires[index] ^= 1;
                } else {
                    fault.digest_wires[index] ^= 1;
                }
                assert_ne!(bound_challenge(&fault), baseline, "map{map} index{index}");
            }
        }
        for endpoint in 0..2 {
            for bit in 0..ID_BITS {
                let mut fault = layout.clone();
                if endpoint == 0 {
                    fault.start[bit / 8] ^= 1 << (bit % 8);
                } else {
                    fault.tip[bit / 8] ^= 1 << (bit % 8);
                }
                assert_ne!(
                    bound_challenge(&fault),
                    baseline,
                    "endpoint{endpoint} bit{bit}"
                );
            }
        }
        let mut wrong_role = layout.clone();
        wrong_role.profile = PROFILE;
        assert_ne!(bound_challenge(&wrong_role), baseline);
        let legacy = header_order::metadata_relation(1, -17).unwrap();
        let analytic = HeaderAdjacencyLayout::compile_metadata(1, 0, -17).unwrap();
        let (r, u, v) = (point(9, 13), point(20, 53), point(20, 109));
        assert_eq!(
            analytic.coefficients(&r, &u, &v).unwrap(),
            legacy.wiring_coefficients(&r, &u, &v).unwrap()
        );
    }

    #[test]
    fn header_id_binding_retains_c3_snapshot() {
        let (start, tip) = (endpoint(7), endpoint(91));
        let layout = HeaderAdjacencyLayout::compile(3, 2, start, tip).unwrap();
        assert_eq!(layout.profile, PROFILE);
        // Frozen C3 descriptor encoding: literals identify the original public
        // transcript contract, independently of the new role dispatch.
        let mut reference = Transcript::new(b"header-adjacency-binding-test");
        reference.append_bytes(
            b"historical-adjacency-profile",
            b"historical-header-parent-digest-adjacency-v1",
        );
        reference.append_u64(b"historical-adjacency-version", 1);
        reference.append_u64(b"historical-adjacency-owners", 3);
        reference.append_u64(b"historical-adjacency-slot-log", 2);
        reference.append_u64(b"historical-adjacency-input-log", 22);
        reference.append_u64(b"historical-adjacency-row-log", 11);
        reference.append_u64(b"historical-adjacency-local-input-log", 20);
        reference.append_u64(b"historical-adjacency-local-row-log", 9);
        let fields = serializer::build(None).unwrap().layout.fields;
        for bit in 0..256 {
            reference.append_u64(
                b"historical-adjacency-parent-wire",
                (header_hash::SERIALIZER_OFFSET + fields.parent_id[bit / 8][bit % 8]) as u64,
            );
            reference.append_u64(
                b"historical-adjacency-digest-wire",
                (segment_relation::DIGEST_OFFSET + bit) as u64,
            );
        }
        reference.append_bytes(b"historical-adjacency-start", &start);
        reference.append_bytes(b"historical-adjacency-tip", &tip);
        assert_eq!(
            bound_challenge(&layout),
            reference.challenge_scalar(b"first-bound-challenge")
        );
    }

    #[test]
    fn metadata_shared_guards_and_prevalidation() {
        for (n, h) in [(0, 0), (2, 0), (3, 1), (1, 22), (i32::MAX as u64 + 1, 21)] {
            assert!(HeaderAdjacencyLayout::compile_metadata(n, h, 1).is_err());
            assert!(HeaderAdjacencyLayout::compile_owned_maps(
                n,
                h,
                [0; 32],
                [0; 32],
                METADATA_PROFILE,
                || { panic!("invalid dimensions reached the canonical map factory") }
            )
            .is_err());
        }
        let layout = HeaderAdjacencyLayout::compile_metadata(3, 2, 30).unwrap();
        let mut calls = 0;
        assert!(layout
            .visit_slot_terms(3, |_, _| {
                calls += 1;
                Ok(())
            })
            .is_err());
        assert_eq!(calls, 0);
        for field in 0..2 {
            let mut fault = layout.clone();
            if field == 0 {
                fault.input_len = 0;
            } else {
                fault.row_count = 0;
            }
            assert!(fault
                .visit_slot_terms(1, |_, _| {
                    calls += 1;
                    Ok(())
                })
                .is_err());
            assert_eq!(calls, 0);
        }
    }
}
