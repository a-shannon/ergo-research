//! Verifier-owned short Legacy DAA templates and physical serializer imports.
//! These fixed imports identify header slots; authentication of those slots and
//! inclusion in the common GKR/PCS roster are separate consumer obligations.
use crate::{
    daa_count,
    daa_finish::{self, CompiledFinish},
    daa_integer::{ShortLegacyInputs, ShortLegacyProfile, TwoRatioInputs},
    gkr::Gate,
    header_hash,
    mapped_daa_plan::{MappedDaaPlan, MAPPED_INPUT_LOG},
    serializer,
    sparse::{self, Circuit, Term},
    transcript::Transcript,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use blake2::{digest::consts::U32, Blake2b, Digest};

const ALIAS_ROW_LOG: usize = 10;
const ARITHMETIC_ROW_LOG: usize = 17;
const SLOT_LEN: usize = 1 << MAPPED_INPUT_LOG;
const EPOCH: usize = 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Profile {
    M2,
    M3,
    M4,
    M5,
    M6,
    M7,
}
impl Profile {
    pub(crate) fn count(self) -> usize {
        match self {
            Self::M2 => 2,
            Self::M3 => 3,
            Self::M4 => 4,
            Self::M5 => 5,
            Self::M6 => 6,
            Self::M7 => 7,
        }
    }
    pub(crate) fn child_height(self) -> usize {
        (self.count() + 1) * EPOCH + 1
    }
    fn seed(self) -> Result<CompiledFinish, String> {
        let m = self.count();
        // Values choose a compiler template only. No seed witness or RAW pin is
        // trusted by the verifier; only the native fixed relation is retained.
        let timestamps = (0..=m).map(|i| i as i64 * 1000).collect::<Vec<_>>();
        if self == Self::M2 {
            daa_finish::compile_two_finish_with_child(
                &daa_count::q(),
                TwoRatioInputs {
                    nbits: [0x0300_0001; 2],
                    timestamps: timestamps.try_into().map_err(|_| "M2 seed width")?,
                },
                0x0300_0001,
                true,
            )
        } else {
            let profile = match self {
                Self::M3 => ShortLegacyProfile::M3,
                Self::M4 => ShortLegacyProfile::M4,
                Self::M5 => ShortLegacyProfile::M5,
                Self::M6 => ShortLegacyProfile::M6,
                Self::M7 => ShortLegacyProfile::M7,
                Self::M2 => unreachable!(),
            };
            daa_finish::compile_short_legacy_with_child(
                &daa_count::q(),
                ShortLegacyInputs {
                    profile,
                    nbits: vec![0x0300_0001; m],
                    timestamps,
                },
                0x0300_0001,
                true,
            )
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Port {
    source_slot: usize,
    serializer_wire: usize,
    daa_wire: usize,
}

pub(crate) struct ShortDaaLayout {
    profile: Profile,
    headers: u64,
    slot_log: usize,
    template: CompiledFinish,
    mapped: MappedDaaPlan,
    map_id: [u8; 32],
    shape: sparse::Shape,
    ports: Vec<Port>,
    descriptor: [u8; 32],
}

/// A private complete M2 alias window, never a whole S12 packet source.
#[cfg(test)]
pub(crate) struct M2AliasEndpointIndex<'a> {
    source:&'a ShortDaaLayout,
    left:std::collections::BTreeMap<usize,Vec<usize>>,
    right:Vec<usize>,
}
#[cfg(test)]
impl<'a> M2AliasEndpointIndex<'a> {
    pub(crate) fn identity(&self)->([u8;32],[u8;32]) {(self.source.map_id,self.source.descriptor)}
    pub(crate) fn visit(&self,profile:Profile,map:[u8;32],descriptor:[u8;32],left:bool,slot:usize,
        mut sink:impl FnMut(usize,Term)->Result<(),String>)->Result<usize,String> {
        if profile!=Profile::M2 || (map,descriptor)!=self.identity() || slot>=4096 {
            return Err("M2 endpoint scope or identity rejected".into());
        }
        let indices:&[usize]=if left {self.left.get(&slot).map(Vec::as_slice).unwrap_or(&[])}
            else if slot==3072 {&self.right} else {&[]};
        let mut count=0usize;
        for &index in indices {sink(index,self.source.alias_term(index)?)?;count+=1;}
        Ok(count)
    }
}
impl ShortDaaLayout {
    fn alias_term(&self,index:usize)->Result<Term,String> {
        let target=self.profile.child_height()-1;
        let port=self.ports.get(index).ok_or("short alias index outside source")?;
        Ok(Term {row:(target<<ALIAS_ROW_LOG)+index,gate:Gate {
            left:port.source_slot*SLOT_LEN+port.serializer_wire,
            right:target*SLOT_LEN+port.daa_wire,c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}})
    }
    #[cfg(test)]
    pub(crate) fn m2_endpoint_index(&self)->Result<M2AliasEndpointIndex<'_>,String> {
        if self.profile!=Profile::M2 || self.headers!=3073 || self.slot_log!=12 || self.ports.len()!=288
            || derive_ports(self.profile,&self.template,&self.mapped)?!=self.ports
            || descriptor(self.profile,self.headers,self.slot_log,self.map_id,&self.ports)!=self.descriptor {
            return Err("named M2 alias source rejected".into());
        }
        let mut left=std::collections::BTreeMap::<usize,Vec<usize>>::new();
        let mut right=Vec::with_capacity(288);
        for (index,port) in self.ports.iter().enumerate() {
            left.entry(port.source_slot).or_default().push(index);right.push(index);
        }
        Ok(M2AliasEndpointIndex{source:self,left,right})
    }

    pub(crate) fn compile(profile: Profile, headers: u64, slot_log: usize) -> Result<Self, String> {
        if slot_log > 21
            || headers < profile.child_height() as u64
            || headers > (1u64 << slot_log)
            || headers.next_power_of_two().trailing_zeros() as usize != slot_log
        {
            return Err("short DAA history count or slot domain rejected".into());
        }
        let template = profile.seed()?;
        let mapped = MappedDaaPlan::compile_short(&template)?;
        let shape = sparse::validate(mapped.circuit(), 0)
            .map_err(|e| format!("short mapped shape rejected: {e:?}"))?;
        if shape.input_bits != MAPPED_INPUT_LOG || shape.row_bits != ARITHMETIC_ROW_LOG {
            return Err("short mapped arithmetic dimensions changed".into());
        }
        let ports = derive_ports(profile, &template, &mapped)?;
        let map_id = mapped.map_identity();
        let descriptor = descriptor(profile, headers, slot_log, map_id, &ports);
        Ok(Self {
            profile,
            headers,
            slot_log,
            template,
            mapped,
            map_id,
            shape,
            ports,
            descriptor,
        })
    }

    /// Producer admission against the consumer's own circuit and handle maps.
    /// Witness validity is subsequently checked by the native residual proof.
    pub(crate) fn admit(&self, compiled: &CompiledFinish) -> Result<MappedDaaPlan, String> {
        let actual = &compiled.joined.joined.joined;
        let expected = &self.template.joined.joined.joined;
        if actual.external.len() != self.profile.count() {
            return Err("short DAA profile source count mismatch".into());
        }
        let geometry = |c: &crate::daa_integer::Count| {
            [
                c.live_bits,
                c.input_bits,
                c.padded_input_bits,
                c.residual_rows,
                c.padded_rows,
                c.terms,
                c.padding_bits,
            ]
        };
        if geometry(&actual.count) != geometry(&expected.count)
            || compiled.increment != self.template.increment
            || compiled.joined.increment != self.template.joined.increment
            || compiled.joined.joined.increment != self.template.joined.joined.increment
        {
            return Err("short DAA native geometry or checkpoint mismatch".into());
        }
        if actual.circuit.as_ref() != expected.circuit.as_ref() {
            return Err("short DAA native relation mismatch".into());
        }
        if compiled.child_nbits != self.template.child_nbits
            || compiled.output.numeric_result != self.template.output.numeric_result
            || actual
                .external
                .iter()
                .zip(&expected.external)
                .any(|(a, b)| {
                    a.nbits != b.nbits
                        || a.start_timestamp != b.start_timestamp
                        || a.end_timestamp != b.end_timestamp
                })
        {
            return Err("short DAA native field handle mismatch".into());
        }
        let mapped = MappedDaaPlan::compile_short(compiled)?;
        self.validate_mapped(&mapped)?;
        if derive_ports(self.profile, compiled, &mapped)? != self.ports {
            return Err("short DAA physical import map mismatch".into());
        }
        Ok(mapped)
    }

    pub(crate) fn validate_mapped(&self, mapped: &MappedDaaPlan) -> Result<(), String> {
        if mapped.map_identity() != self.map_id {
            return Err("short DAA mapped identity mismatch".into());
        }
        Ok(())
    }
    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        transcript.append_bytes(
            b"short-daa-profile",
            b"legacy-m2-m7-increasing-times-physical-v1",
        );
        transcript.append_bytes(b"short-daa-descriptor", &self.descriptor);
    }
    pub(crate) fn descriptor(&self) -> [u8; 32] {
        self.descriptor
    }
    pub(crate) fn mapped_relation(&self) -> &Circuit {
        self.mapped.circuit()
    }
    pub(crate) fn visit_alias_terms(
        &self,
        mut sink: impl FnMut(Term) -> Result<(), String>,
    ) -> Result<usize, String> {
        for index in 0..self.ports.len() {
            sink(self.alias_term(index)?)?;
        }
        Ok(self.ports.len())
    }
    pub(crate) fn alias_coefficients(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], String> {
        if r.len() != ALIAS_ROW_LOG + self.slot_log
            || u.len() != MAPPED_INPUT_LOG + self.slot_log
            || v.len() != u.len()
        {
            return Err("short DAA alias point dimensions rejected".into());
        }
        let mut out = [Fr::zero(); 4];
        self.visit_alias_terms(|term| {
            let weight = eq_at(r, term.row) * eq_at(u, term.gate.left) * eq_at(v, term.gate.right);
            out[1] += weight;
            out[2] -= weight;
            Ok(())
        })?;
        Ok(out)
    }
    pub(crate) fn arithmetic_coefficients(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], String> {
        if r.len() != ARITHMETIC_ROW_LOG + self.slot_log
            || u.len() != MAPPED_INPUT_LOG + self.slot_log
            || v.len() != u.len()
        {
            return Err("short DAA arithmetic point dimensions rejected".into());
        }
        let mut out = sparse::wiring(
            self.mapped.circuit(),
            &self.shape,
            &r[..ARITHMETIC_ROW_LOG],
            &u[..MAPPED_INPUT_LOG],
            &v[..MAPPED_INPUT_LOG],
        )
        .map_err(|e| format!("short wiring rejected: {e:?}"))?;
        let target = self.profile.child_height() - 1;
        let factor = eq_at(&r[ARITHMETIC_ROW_LOG..], target)
            * eq_at(&u[MAPPED_INPUT_LOG..], target)
            * eq_at(&v[MAPPED_INPUT_LOG..], target);
        for coefficient in &mut out {
            *coefficient *= factor;
        }
        Ok(out)
    }
}

fn derive_ports(
    profile: Profile,
    compiled: &CompiledFinish,
    mapped: &MappedDaaPlan,
) -> Result<Vec<Port>, String> {
    let m = profile.count();
    let window = &compiled.joined.joined.joined;
    if window.external.len() != m
        || window
            .external
            .windows(2)
            .any(|pair| pair[0].end_timestamp != pair[1].start_timestamp)
    {
        return Err("short DAA shared timestamp handles rejected".into());
    }
    let child = compiled
        .child_nbits
        .as_ref()
        .ok_or("short child handles missing")?;
    let serializer = serializer::build(None)?;
    let fields = &serializer.layout.fields;
    let mut ports = Vec::with_capacity(96 * (m + 1));
    let mut append =
        |source_slot: usize, serializer_wire: usize, source_wire: usize| -> Result<(), String> {
            let serializer_wire = header_hash::SERIALIZER_OFFSET
                .checked_add(serializer_wire)
                .ok_or("serializer offset overflow")?;
            let daa_wire = mapped.mapped_wire(source_wire)?;
            if serializer_wire >= SLOT_LEN
                || daa_wire >= SLOT_LEN
                || source_slot > profile.child_height() - 1
            {
                return Err("short DAA physical port escapes owner domain".into());
            }
            ports.push(Port {
                source_slot,
                serializer_wire,
                daa_wire,
            });
            Ok(())
        };
    for i in 0..=m {
        let wires = if i == m {
            &window.external[m - 1].end_timestamp
        } else {
            &window.external[i].start_timestamp
        };
        for bit in 0..64 {
            append((i + 1) * EPOCH - 1, fields.timestamp[bit], wires[bit])?;
        }
    }
    for i in 0..m {
        for bit in 0..32 {
            append(
                (i + 2) * EPOCH - 1,
                fields.n_bits[bit],
                window.external[i].nbits[bit],
            )?;
        }
    }
    for bit in 0..32 {
        append(profile.child_height() - 1, fields.n_bits[bit], child[bit])?;
    }
    if ports.len() != 96 * (m + 1) || ports.len() > (1 << ALIAS_ROW_LOG) {
        return Err("short DAA port count mismatch".into());
    }
    Ok(ports)
}
fn descriptor(
    profile: Profile,
    headers: u64,
    slot_log: usize,
    map: [u8; 32],
    ports: &[Port],
) -> [u8; 32] {
    let mut hash = Blake2b::<U32>::new();
    hash.update(b"short-legacy-native-physical-descriptor-v1");
    for value in [
        profile.count() as u64,
        profile.child_height() as u64,
        headers,
        slot_log as u64,
        ALIAS_ROW_LOG as u64,
        ARITHMETIC_ROW_LOG as u64,
        MAPPED_INPUT_LOG as u64,
        ports.len() as u64,
    ] {
        hash.update(value.to_le_bytes());
    }
    hash.update(map);
    for port in ports {
        for value in [port.source_slot, port.serializer_wire, port.daa_wire] {
            hash.update((value as u64).to_le_bytes());
        }
    }
    hash.finalize().into()
}
fn eq_at(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |weight, (bit, x)| {
            weight
                * if (index >> bit) & 1 == 1 {
                    *x
                } else {
                    Fr::one() - x
                }
        })
}
