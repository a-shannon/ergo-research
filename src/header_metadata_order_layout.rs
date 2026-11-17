//! Bounded shared-witness order and previous/current metadata relations.
//!
//! This module composes the fixed local header-order circuit with a
//! code-owned metadata adjacency descriptor. It does not construct a proof,
//! authenticate header hashes, or establish a full-history claim by itself.

use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    gkr::Gate,
    header_adjacency_layout::HeaderAdjacencyLayout,
    header_order::{self, Compiled as LocalOrder},
    sparse::{self, Shape},
    transcript::Transcript,
    wiring::{self, RightIndex},
    work_tree_layout,
};

const PROFILE: &[u8] = b"historical-header-metadata-order-composite-v1";
const VERSION: u64 = 1;
const MAX_SLOT_LOG: usize = 21;
const LOCAL_INPUT_LOG: usize = 20;
const LOCAL_INPUT_WIDTH: usize = 1 << LOCAL_INPUT_LOG;
const LOCAL_ROW_LOG: usize = 12;
const LOCAL_ROW_WIDTH: usize = 1 << LOCAL_ROW_LOG;
const ORDER_ROW_LOG: usize = 11;
const ORDER_INPUT_LOG: usize = 10;
const FAMILY_BIT: usize = 11;
const MEMBER_WIDTH: usize = 1 << FAMILY_BIT;
const METADATA_FAMILY_BASE: usize = 1 << FAMILY_BIT;
const METADATA_MEMBER_DOMAIN: usize = 1 << 9;
const ORDER_TERM_COUNT: usize = 2081;
const METADATA_BITS: usize = 256;
const TERMS_PER_OWNER: usize = ORDER_TERM_COUNT + METADATA_BITS;

/// Immutable dimensions and code-owned relations for one bounded history.
pub(crate) struct HeaderMetadataOrderLayout {
    n: u64,
    slot_log: usize,
    input_log: usize,
    row_log: usize,
    input_len: usize,
    row_count: usize,
    term_count: usize,
    metadata: HeaderAdjacencyLayout,
    order: LocalOrder,
    order_shape: Shape,
    order_fingerprint: String,
}

fn eq_index(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |acc, (bit, value)| {
            acc * if (index >> bit) & 1 == 1 {
                *value
            } else {
                Fr::one() - value
            }
        })
}

fn eq_zero(point: &[Fr]) -> Fr {
    point
        .iter()
        .fold(Fr::one(), |acc, value| acc * (Fr::one() - value))
}

impl HeaderMetadataOrderLayout {
    pub(crate) fn compile(n: u64, slot_log: usize, tip_time: i64) -> Result<Self, String> {
        if usize::BITS < 64 {
            return Err("metadata/order layout requires 64-bit platform indices".into());
        }
        if slot_log > MAX_SLOT_LOG {
            return Err("metadata/order slot logarithm exceeds profile".into());
        }
        let owner_domain = 1u64
            .checked_shl(u32::try_from(slot_log).map_err(|_| "slot logarithm conversion overflow")?)
            .ok_or("metadata/order owner domain overflow")?;
        if n == 0 || n > owner_domain || n > i32::MAX as u64 {
            return Err("metadata/order owner count outside admitted domain".into());
        }

        let metadata = HeaderAdjacencyLayout::compile_metadata(n, slot_log, tip_time)?;
        let order = header_order::local_order()?;
        if order.circuit.terms.len() != ORDER_TERM_COUNT
            || order.circuit.input_len != (1 << ORDER_INPUT_LOG)
            || order.circuit.row_count != (1 << ORDER_ROW_LOG)
        {
            return Err("canonical local order shape changed".into());
        }
        let order_shape = sparse::validate(&order.circuit, 0)
            .map_err(|error| format!("canonical local order validation failed: {error:?}"))?;
        if order_shape.input_bits != ORDER_INPUT_LOG
            || order_shape.row_bits != ORDER_ROW_LOG
            || order_shape.copies != 1
        {
            return Err("canonical local order sparse shape changed".into());
        }

        let input_log = LOCAL_INPUT_LOG
            .checked_add(slot_log)
            .ok_or("metadata/order input logarithm overflow")?;
        let row_log = LOCAL_ROW_LOG
            .checked_add(slot_log)
            .ok_or("metadata/order row logarithm overflow")?;
        let input_len = 1usize
            .checked_shl(u32::try_from(input_log).map_err(|_| "input log conversion overflow")?)
            .ok_or("metadata/order input dimension overflow")?;
        let row_count = 1usize
            .checked_shl(u32::try_from(row_log).map_err(|_| "row log conversion overflow")?)
            .ok_or("metadata/order row dimension overflow")?;
        let owners = usize::try_from(n).map_err(|_| "owner count does not fit usize")?;
        let term_count = owners
            .checked_mul(TERMS_PER_OWNER)
            .and_then(|count| count.checked_add(METADATA_BITS))
            .ok_or("metadata/order term count overflow")?;
        if metadata.n() != n
            || metadata.slot_log() != slot_log
            || metadata.input_log() != input_log
            || metadata.row_log().checked_add(3) != Some(row_log)
            || metadata.term_count()
                != owners
                    .checked_add(1)
                    .and_then(|count| count.checked_mul(METADATA_BITS))
                    .ok_or("metadata adjacency term count overflow")?
        {
            return Err("metadata adjacency descriptor disagrees with composite domain".into());
        }

        let order_fingerprint = work_tree_layout::hash_terms(&order.circuit.terms);
        Ok(Self {
            n,
            slot_log,
            input_log,
            row_log,
            input_len,
            row_count,
            term_count,
            metadata,
            order,
            order_shape,
            order_fingerprint,
        })
    }

    pub(crate) fn n(&self) -> u64 {
        self.n
    }
    pub(crate) fn slot_log(&self) -> usize {
        self.slot_log
    }
    pub(crate) fn input_log(&self) -> usize {
        self.input_log
    }
    pub(crate) fn row_log(&self) -> usize {
        self.row_log
    }
    pub(crate) fn input_len(&self) -> usize {
        self.input_len
    }
    pub(crate) fn row_count(&self) -> usize {
        self.row_count
    }
    pub(crate) fn term_count(&self) -> usize {
        self.term_count
    }

    /// Bind the exact metadata maps/endpoints and local circuit before the
    /// consumer samples any challenge.
    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        self.bind_with_identity(transcript, PROFILE, VERSION, &header_order::MAINNET_GENESIS);
    }

    // Private fault seam; public construction and binding use only code-owned
    // identity constants. No caller-supplied identity reaches the consumer.
    fn bind_with_identity(
        &self,
        transcript: &mut Transcript,
        profile: &[u8],
        version: u64,
        genesis: &[u8; 32],
    ) {
        self.metadata.bind(transcript);
        transcript.append_bytes(b"historical-metadata-order-profile", profile);
        transcript.append_u64(b"historical-metadata-order-version", version);
        transcript.append_u64(b"historical-metadata-order-n", self.n);
        transcript.append_u64(b"historical-metadata-order-slot-log", self.slot_log as u64);
        transcript.append_u64(
            b"historical-metadata-order-input-length",
            self.input_len as u64,
        );
        transcript.append_u64(
            b"historical-metadata-order-input-log",
            self.input_log as u64,
        );
        transcript.append_u64(
            b"historical-metadata-order-row-count",
            self.row_count as u64,
        );
        transcript.append_u64(b"historical-metadata-order-row-log", self.row_log as u64);
        transcript.append_u64(
            b"historical-metadata-order-term-count",
            self.term_count as u64,
        );
        transcript.append_u64(b"historical-metadata-order-family-bit", FAMILY_BIT as u64);
        transcript.append_u64(
            b"historical-metadata-order-member-width",
            MEMBER_WIDTH as u64,
        );
        transcript.append_u64(
            b"historical-metadata-order-metadata-base",
            METADATA_FAMILY_BASE as u64,
        );
        transcript.append_u64(
            b"historical-metadata-order-member-domain",
            METADATA_MEMBER_DOMAIN as u64,
        );
        transcript.append_u64(
            b"historical-metadata-order-row-width",
            LOCAL_ROW_WIDTH as u64,
        );
        transcript.append_u64(
            b"historical-metadata-order-order-bank-offset",
            header_order::ORDER_OFFSET as u64,
        );
        transcript.append_u64(
            b"historical-metadata-order-order-bank-prefix",
            (header_order::ORDER_OFFSET >> ORDER_INPUT_LOG) as u64,
        );
        transcript.append_u64(
            b"historical-metadata-order-local-count",
            ORDER_TERM_COUNT as u64,
        );
        transcript.append_u64(
            b"historical-metadata-order-local-input-log",
            ORDER_INPUT_LOG as u64,
        );
        transcript.append_u64(
            b"historical-metadata-order-local-row-log",
            ORDER_ROW_LOG as u64,
        );
        transcript.append_u64(
            b"historical-metadata-order-local-copies",
            self.order_shape.copies as u64,
        );
        transcript.append_bytes(
            b"historical-metadata-order-local-circuit",
            self.order_fingerprint.as_bytes(),
        );
        transcript.append_bytes(b"historical-metadata-order-genesis", genesis);
    }

    /// Emit one owner’s terms. Both families and every translation are
    /// prevalidated before the caller’s sink can observe a term.
    pub(crate) fn visit_slot_terms(
        &self,
        slot: u64,
        mut sink: impl FnMut(usize, Gate) -> Result<(), String>,
    ) -> Result<usize, String> {
        if slot >= self.n {
            return Err("metadata/order slot outside active owner history".into());
        }
        let owner = usize::try_from(slot).map_err(|_| "slot does not fit usize")?;
        let row_base = owner
            .checked_mul(LOCAL_ROW_WIDTH)
            .ok_or("metadata/order row translation overflow")?;
        let row_last = row_base
            .checked_add(LOCAL_ROW_WIDTH - 1)
            .filter(|row| *row < self.row_count)
            .ok_or("metadata/order owner rows outside global domain")?;
        let input_base = owner
            .checked_mul(LOCAL_INPUT_WIDTH)
            .ok_or("metadata/order input translation overflow")?;
        let input_last = input_base
            .checked_add(LOCAL_INPUT_WIDTH - 1)
            .filter(|wire| *wire < self.input_len)
            .ok_or("metadata/order owner inputs outside global domain")?;
        let order_bank_base = input_base
            .checked_add(header_order::ORDER_OFFSET)
            .ok_or("order bank input translation overflow")?;
        for term in &self.order.circuit.terms {
            if term.row >= (1 << ORDER_ROW_LOG)
                || term.gate.left >= (1 << ORDER_INPUT_LOG)
                || term.gate.right >= (1 << ORDER_INPUT_LOG)
            {
                return Err("order term outside its canonical local domain".into());
            }
            let row = row_base
                .checked_add(term.row)
                .filter(|row| *row <= row_last && *row < self.row_count)
                .ok_or("order row translation outside global domain")?;
            for wire in [term.gate.left, term.gate.right] {
                order_bank_base
                    .checked_add(wire)
                    .filter(|translated| *translated <= input_last && *translated < self.input_len)
                    .ok_or("order wire translation outside global domain")?;
            }
            let _ = row;
        }

        let metadata_row_base = owner
            .checked_mul(METADATA_MEMBER_DOMAIN)
            .ok_or("metadata source row translation overflow")?;
        let mut metadata_count = 0usize;
        self.metadata.visit_slot_terms(slot, |row, gate| {
            let member = row
                .checked_sub(metadata_row_base)
                .filter(|member| *member < METADATA_MEMBER_DOMAIN)
                .ok_or("metadata source row is outside owner slot")?;
            let translated_row = row_base
                .checked_add(METADATA_FAMILY_BASE)
                .and_then(|base| base.checked_add(member))
                .filter(|row| *row <= row_last && *row < self.row_count)
                .ok_or("metadata row translation outside composite domain")?;
            // The generic metadata emitter already returns global input
            // endpoints, including the predecessor owner and GLOBAL0 anchors.
            // Only its row geometry changes in this composite.
            if gate.left >= self.input_len || gate.right >= self.input_len {
                return Err("metadata global input outside composite domain".into());
            }
            metadata_count = metadata_count
                .checked_add(1)
                .ok_or("metadata prevalidation count overflow")?;
            let _ = translated_row;
            Ok(())
        })?;
        let expected_metadata = METADATA_BITS
            .checked_mul((slot == 0) as usize + (slot > 0) as usize + (slot + 1 == self.n) as usize)
            .ok_or("metadata slot term count overflow")?;
        if metadata_count != expected_metadata {
            return Err("metadata slot emitted count disagrees with anchors and links".into());
        }

        let mut emitted = 0usize;
        for term in &self.order.circuit.terms {
            let row = row_base + term.row;
            let gate = Gate {
                left: order_bank_base + term.gate.left,
                right: order_bank_base + term.gate.right,
                c0: term.gate.c0,
                c1: term.gate.c1,
                c2: term.gate.c2,
                c3: term.gate.c3,
            };
            sink(row, gate)?;
            emitted += 1;
        }
        self.metadata.visit_slot_terms(slot, |row, gate| {
            let member = row - metadata_row_base;
            let translated_row = row_base + METADATA_FAMILY_BASE + member;
            sink(translated_row, gate)?;
            emitted += 1;
            Ok(())
        })?;
        Ok(emitted)
    }

    /// Evaluate all four gate coefficients without enumerating owner slots.
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != self.row_log || u.len() != self.input_log || v.len() != self.input_log {
            return Err("metadata/order coefficient point dimensions rejected".into());
        }
        let local_order = sparse::wiring(
            &self.order.circuit,
            &self.order_shape,
            &r[..ORDER_ROW_LOG],
            &u[..ORDER_INPUT_LOG],
            &v[..ORDER_INPUT_LOG],
        )
        .map_err(|error| format!("local order coefficient evaluation failed: {error:?}"))?;
        let order_bank = eq_index(
            &u[ORDER_INPUT_LOG..LOCAL_INPUT_LOG],
            header_order::ORDER_OFFSET >> ORDER_INPUT_LOG,
        ) * eq_index(
            &v[ORDER_INPUT_LOG..LOCAL_INPUT_LOG],
            header_order::ORDER_OFFSET >> ORDER_INPUT_LOG,
        );
        let family_order = eq_zero(&r[FAMILY_BIT..FAMILY_BIT + 1]);
        let order_owners = wiring::evaluate_shift(
            &r[LOCAL_ROW_LOG..],
            &u[LOCAL_INPUT_LOG..],
            &v[LOCAL_INPUT_LOG..],
            0,
            0,
            self.n,
            0,
            RightIndex::SameRow,
        )?;
        let order_factor = order_bank * family_order * order_owners;

        let mut metadata_row = Vec::with_capacity(9 + self.slot_log);
        metadata_row.extend_from_slice(&r[..9]);
        metadata_row.extend_from_slice(&r[LOCAL_ROW_LOG..]);
        let metadata = self.metadata.coefficients(&metadata_row, u, v)?;
        let metadata_family = r[FAMILY_BIT] * eq_zero(&r[9..FAMILY_BIT]);
        let mut result = [Fr::zero(); 4];
        for index in 0..4 {
            result[index] = local_order[index] * order_factor + metadata[index] * metadata_family;
        }
        Ok(result)
    }
}

// source28-role6-endpoint-BEGIN
#[cfg(test)]
#[derive(Default,Clone,Debug)]
pub(crate) struct Role6EndpointStats {
    pub source_emitter_calls:u64,pub canonical_callbacks:u64,pub selected_callbacks:u64,
    pub order_term_prevalidations:u64,pub order_wire_prevalidations:u64,pub metadata_term_prevalidations:u64,
    pub adjacency_calls:u64,pub adjacency_wire_iterations:u64,pub adjacency_wire_endpoint_checks:u64,
}
#[cfg(test)]
impl Role6EndpointStats {
    fn add(value:&mut u64,n:u64)->Result<(),String>{*value=value.checked_add(n).ok_or("role6 adapter counter overflow")?;Ok(())}
    fn completed_source(&mut self,owner:usize,metadata:u64)->Result<(),String>{
        // These are source-derived loop counts for a successfully completed call,
        // outside its sink callbacks. They are not instrumentation of helper time.
        Self::add(&mut self.order_term_prevalidations,2081)?;
        Self::add(&mut self.order_wire_prevalidations,4162)?;
        Self::add(&mut self.metadata_term_prevalidations,metadata)?;
        Self::add(&mut self.adjacency_calls,2)?;Self::add(&mut self.adjacency_wire_iterations,1024)?;
        Self::add(&mut self.adjacency_wire_endpoint_checks,if owner>0{2048}else{1024})
    }
}
#[cfg(test)]
impl HeaderMetadataOrderLayout {
    pub(crate) fn role6_endpoint_shape_for_test(&self)->Result<(),String>{
        if self.slot_log>12||self.n==0||self.n>1u64<<self.slot_log||self.input_log!=20+self.slot_log
            ||self.row_log!=12+self.slot_log||self.input_len!=1usize<<self.input_log||self.row_count!=1usize<<self.row_log
            ||self.order.circuit.terms.len()!=2081||self.order.circuit.input_len!=1024||self.order.circuit.row_count!=2048
            ||self.term_count!=2337usize.checked_mul(self.n as usize).and_then(|n|n.checked_add(256)).ok_or("role6 endpoint count overflow")?{
            return Err("role6 endpoint canonical shape".into());}Ok(())
    }
    pub(crate) fn visit_endpoint_for_test(&self,left:bool,requested:usize,stats:&mut Role6EndpointStats,
        sink:&mut dyn FnMut(crate::sparse_stream_roster::EdgeTerm)->Result<(),String>)->Result<(),String>{
        self.role6_endpoint_shape_for_test()?;let owners=1usize<<self.slot_log;
        if requested>=owners{return Err("role6 endpoint owner range".into());}
        let n=self.n as usize;if requested>=n{return Ok(());}
        let mut sources=[requested,usize::MAX];
        if left&&requested+1<n{sources[1]=requested+1;}
        if !left&&requested==0&&n>1{sources[1]=n-1;}
        for owner in sources.into_iter().filter(|p|*p!=usize::MAX){
            Role6EndpointStats::add(&mut stats.source_emitter_calls,1)?;
            let mut metadata=0u64;
            self.visit_slot_terms(owner as u64,|row,gate|{
                Role6EndpointStats::add(&mut stats.canonical_callbacks,1)?;
                if row&4095>=2048{metadata=metadata.checked_add(1).ok_or("role6 metadata counter overflow")?;}
                if row>>12!=owner||row>=self.row_count||gate.left>=self.input_len||gate.right>=self.input_len{
                    return Err("role6 endpoint canonical coordinates".into());}
                let endpoint=if left{gate.left}else{gate.right};if endpoint>>20!=requested{return Ok(());}
                let edge=crate::sparse_stream_roster::EdgeTerm{source_slot:owner,family_row:row&4095,term:crate::sparse::Term{row,gate}};
                if crate::sparse_stream_roster::global_edge_row(owner,edge.family_row,self.slot_log,12,0,&[12])?!=row{
                    return Err("role6 endpoint original row".into());}
                sink(edge)?;Role6EndpointStats::add(&mut stats.selected_callbacks,1)
            })?;
            stats.completed_source(owner,metadata)?;
        }Ok(())
    }
}
#[cfg(test)]
pub(crate) fn role6_endpoint_controls_for_test(){tests::role6_controls();}
// source28-role6-endpoint-END

#[cfg(test)]
mod tests {
    // source28-role6-controls-BEGIN
    pub(super) fn role6_controls(){
        use crate::{gkr,packed::{PackedFile,PackedReaderFault},sparse_stream_roster as edge};
        use ark_ff::PrimeField;
        use std::collections::BTreeMap;
        type Key=(usize,usize,usize,[[u64;4];4]);
        let key=|row:usize,g:&Gate|->Key{(row,g.left,g.right,[g.c0,g.c1,g.c2,g.c3].map(|x|x.into_bigint().0))};
        let layout=HeaderMetadataOrderLayout::compile(3,2,3000).unwrap();
        let reference=reference_gates(3,3000);assert_eq!(reference.len(),7267);
        assert_eq!(reference.iter().map(|(row,_)|*row).collect::<std::collections::BTreeSet<_>>().len(),6601);
        assert_eq!(reference.iter().filter(|(_,g)|!g.c3.is_zero()).count(),3840);
        let mut expected=BTreeMap::<Key,usize>::new();for(row,g)in &reference{*expected.entry(key(*row,g)).or_default()+=1;}
        assert!(expected.len()*512+reference.capacity()*std::mem::size_of::<(usize,Gate)>()<8*1024*1024);
        for left in [true,false]{let mut actual=BTreeMap::<Key,usize>::new();let mut counts=[0usize;4];let mut stats=Role6EndpointStats::default();
            for owner in 0..4{layout.visit_endpoint_for_test(left,owner,&mut stats,&mut|e|{
                assert_eq!(e.term.row,edge::global_edge_row(e.source_slot,e.family_row,2,12,0,&[12]).unwrap());
                assert!(actual.len()<7268);*actual.entry(key(e.term.row,&e.term.gate)).or_default()+=1;counts[owner]+=1;Ok(())}).unwrap();}
            assert_eq!(counts,[2593,2337,2337,0]);assert_eq!(actual,expected);assert_eq!(stats.selected_callbacks,7267);
            assert_eq!(stats.canonical_callbacks,if left{12197}else{9860});
        }
        let one=HeaderMetadataOrderLayout::compile(1,0,1000).unwrap();
        for left in [true,false]{let mut stats=Role6EndpointStats::default();one.visit_endpoint_for_test(left,0,&mut stats,&mut |_|Ok(())).unwrap();
            assert_eq!((stats.source_emitter_calls,stats.canonical_callbacks,stats.selected_callbacks),(1,2593,2593));}
        let mut used=0;assert_eq!(layout.visit_endpoint_for_test(true,4,&mut Role6EndpointStats::default(),&mut |_|{used+=1;Ok(())}).unwrap_err(),"role6 endpoint owner range");assert_eq!(used,0);
        for fault in 0..5{let mut wrong=HeaderMetadataOrderLayout::compile(3,2,3000).unwrap();match fault{0=>wrong.slot_log=usize::MAX,1=>wrong.row_log+=1,
            2=>wrong.input_log+=1,3=>wrong.term_count-=1,_=>wrong.n=0};
            assert_eq!(wrong.visit_endpoint_for_test(true,0,&mut Role6EndpointStats::default(),&mut |_|{used+=1;Ok(())}).unwrap_err(),"role6 endpoint canonical shape");assert_eq!(used,0);}
        let mut overflow=Role6EndpointStats{source_emitter_calls:u64::MAX,..Default::default()};
        assert_eq!(layout.visit_endpoint_for_test(true,0,&mut overflow,&mut |_|Ok(())).unwrap_err(),"role6 adapter counter overflow");
        assert_eq!(layout.visit_endpoint_for_test(true,0,&mut Role6EndpointStats::default(),&mut |_|Err("role6 isolated sink".into())).unwrap_err(),"role6 isolated sink");
        // Each algebra mutant differs at a selected Boolean row/endpoint basis.
        for range in [0..1024,1794..1795,1795..1859]{let(row,g)=reference.iter().find(|(r,g)|range.contains(r)&&!g.c3.is_zero()).unwrap();
            let r=bool_point(*row,14);let u=bool_point(g.left,22);let v=bool_point(g.right,22);let mut mutant=reference.clone();
            let pos=reference.iter().position(|(a,b)|a==row&&key(*a,b)==key(*row,g)).unwrap();mutant[pos].1.c3+=Fr::one();
            assert_ne!(direct_coefficients(&reference,&r,&u,&v),direct_coefficients(&mutant,&r,&u,&v));}
        for fault in 0..9{let mut mutant=reference.clone();let i=if fault==0{mutant.iter().position(|(r,g)|*r<2048&&g.c2.is_zero()&&g.c3.is_zero()&&g.right==ORDER_OFFSET).unwrap()}
                else{mutant.iter().position(|(r,_)|*r==((1<<12)+2048)).unwrap()};let original=mutant[i].clone();
            match fault{0=>mutant[i].1.right=0,1=>mutant[i].0-=1<<12,2=>mutant[i].1.left+=1<<20,
                3=>mutant[i].0^=1<<11,4=>mutant[i].1.c0+=Fr::one(),5=>{mutant.remove(i);},6=>mutant.push(original.clone()),
                7=>mutant[i].0=(3<<12)+(original.0&4095),_=>mutant[i].1.left^=1};
            let mut changed=BTreeMap::<Key,usize>::new();for(row,g)in &mutant{*changed.entry(key(*row,g)).or_default()+=1;}assert_ne!(changed,expected);
            let r=bool_point(original.0,14);let u=bool_point(original.1.left,22);let v=bool_point(original.1.right,22);
            let honest=direct_coefficients(&reference,&r,&u,&v);assert!(honest.iter().any(|x|!x.is_zero()));
            assert_ne!(honest,direct_coefficients(&mutant,&r,&u,&v));}
        let anchor=reference.iter().find(|(r,g)|*r>=2048&&g.right==0).unwrap();let mut altered=reference.clone();
        let i=reference.iter().position(|x|x==anchor).unwrap();altered[i].1.right=ORDER_OFFSET;
        assert_ne!(direct_coefficients(&reference,&bool_point(anchor.0,14),&bool_point(anchor.1.left,22),&bool_point(0,22)),
            direct_coefficients(&altered,&bool_point(anchor.0,14),&bool_point(anchor.1.left,22),&bool_point(0,22)));
        // Isolate use of a prefix-folded RIGHT in U's coefficient bank while X
        // and the unchanged reference remain identical. Coefficient adjustment
        // encodes precisely that wrong bank; the actual replay still reads RIGHT.
        let (_,conditional)=reference.iter().find(|(row,g)|*row==1794&&!g.c3.is_zero()).unwrap();
        let term=crate::sparse::Term{row:0,gate:Gate{left:0,right:1,c0:conditional.c0,c1:conditional.c1,c2:conditional.c2,c3:conditional.c3}};
        let weights=edge::EdgeFallbackWeightsForTest::new(&[],&[Fr::from(3u64),Fr::from(5u64)],2);
        let prefix=[Fr::from(2u64)];let original=[Fr::one(),Fr::zero(),Fr::one(),Fr::one()];
        let folded_right=original[0]+prefix[0]*(original[1]-original[0]);assert_ne!(folded_right,original[1]);
        let run=|t:crate::sparse::Term|edge::edge_fallback_prefix_for_test(true,0,2,0,0,0,&[0],1,&weights,Fr::zero(),&prefix,
            |_,_,sink|sink(edge::EdgeTerm{source_slot:0,family_row:0,term:t.clone()}),|_|Ok(original.to_vec()),None).unwrap();
        let honest=run(term.clone());let mut wrong=term.clone();wrong.gate.c1+=term.gate.c3*(folded_right-original[1]);
        wrong.gate.c0+=term.gate.c2*(folded_right-original[1]);assert_ne!(honest.message,run(wrong).message);
        stale_previous_timestamp_delta_recomputed_keeps_local_order_but_breaks_link();
        let banks=[bank(1,1000,0,0,true),bank(2,2000,1,1000,false),bank(3,3000,2,2000,false)];
        let mut packets=vec![vec![0xA5u8;131072];4];for(owner,bank)in banks.iter().enumerate(){
            for(bit,value)in bank.iter().enumerate(){let wire=ORDER_OFFSET+bit;let mask=1u8<<(wire%8);
                if value.is_zero(){packets[owner][wire/8]&=!mask;}else{assert_eq!(*value,Fr::one());packets[owner][wire/8]|=mask;}}}
        let path=std::env::temp_dir().join(format!("role6-n3-{}-{}.bits",std::process::id(),std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let mut file=std::fs::OpenOptions::new().write(true).create_new(true).open(&path).unwrap();
        use std::io::Write;for p in &packets{file.write_all(p).unwrap();}file.sync_all().unwrap();drop(file);drop(packets);
        let source=PackedFile::open(&path,22).unwrap();
        let view=source.h2_boolean_view().unwrap();for fault in [PackedReaderFault::Io,PackedReaderFault::Short,PackedReaderFault::ShortByOneByte]{assert!(view.reader_fault_for_test(0,fault).is_err());}
        let mut kept=None;for(direct,zero_padding)in[(false,false),(true,false),(true,true)]{
            let mut input=edge::PackedEdgeInput::new(1<<20,4,|owner|{let mut packet=source.h2_boolean_view()?.read_copy(owner)?.into_bytes();
                if zero_padding&&owner==3{packet.fill(0);}Ok(packet)}).unwrap();
            let mut t=crate::transcript::Transcript::new(b"role6-n3-full-differential-v1");let mut count=Role6EndpointStats::default();
            let(proof,claim,iu,iv,stats)=edge::prove_edge_terms_strategy_for_test(20,2,12,0,&[12],direct,true,true,0,&mut input,
                |left,owner,sink|layout.visit_endpoint_for_test(left,owner,&mut count,sink),&mut t,|t|layout.bind(t),
                |r,u,v|layout.coefficients(r,u,v),&mut |_|Ok(())).unwrap();drop(input);assert!(!iu&&!iv);
            assert_eq!(stats.term_callbacks,44*7267);assert_eq!(count.selected_callbacks,44*7267);
            let encoded=gkr::encode_proof(&proof).unwrap();assert_eq!(encoded.len(),5024);
            let decoded=gkr::decode_dimensions(&[22],&encoded).unwrap();assert_eq!(gkr::encode_proof(&decoded).unwrap(),encoded);
            let mut fresh=crate::transcript::Transcript::new(b"role6-n3-full-differential-v1");
            let verified=gkr::verify_with_wiring(&[22],1<<14,&decoded,&mut fresh,|t|layout.bind(t),
                |layer,r,u,v|if layer==0{layout.coefficients(r,u,v).map_err(|_|gkr::GkrError::PointDimension)}else{Err(gkr::GkrError::PointDimension)}).unwrap();
            assert_eq!(verified,claim);let held_value=source.evaluate(&claim.point).unwrap();
            if zero_padding{assert_ne!(held_value,claim.value,"zeroed padding X must fail the unchanged held-source consumer");continue;}
            assert_eq!(held_value,claim.value);
            assert_eq!((fresh.challenges(),fresh.raw_queries(),fresh.bytes_absorbed()),(t.challenges(),t.raw_queries(),t.bytes_absorbed()));
            let continuation=t.clone().challenge_scalar(b"role6-n3-next");assert_eq!(continuation,fresh.clone().challenge_scalar(b"role6-n3-next"));
            if let Some((bytes,old_claim,old_next))=&kept{assert_eq!(&encoded,bytes);assert_eq!(&claim,old_claim);assert_eq!(&continuation,old_next);}
            else{kept=Some((encoded,claim,continuation));}
        }drop(source);std::fs::remove_file(path).unwrap();
    }
    // source28-role6-controls-END
    use super::*;
    use crate::header_order::{self, ORDER_OFFSET};

    fn gate(left: usize, right: usize, c0: Fr, c1: Fr, c2: Fr, c3: Fr) -> Gate {
        Gate {
            left,
            right,
            c0,
            c1,
            c2,
            c3,
        }
    }

    fn endpoint_bit(bytes: &[u8; 32], bit: usize) -> Fr {
        Fr::from(((bytes[bit / 8] >> (bit % 8)) & 1) as u64)
    }

    fn bool_point(index: usize, width: usize) -> Vec<Fr> {
        (0..width)
            .map(|bit| Fr::from(((index >> bit) & 1) as u64))
            .collect()
    }

    fn dense_point(width: usize, seed: u64) -> Vec<Fr> {
        (0..width)
            .map(|bit| Fr::from(seed + bit as u64 * 37 + 3))
            .collect()
    }

    fn direct_eq(point: &[Fr], index: usize) -> Fr {
        let mut result = Fr::one();
        for bit in 0..point.len() {
            result *= if (index >> bit) & 1 == 1 {
                point[bit]
            } else {
                Fr::one() - point[bit]
            };
        }
        result
    }

    /// Direct indexed specification of the local equations. Unlike the
    /// production factory, this derives each term from its ordinal, without
    /// reading local_order, row ranges, or any producer/consumer helper.
    fn reference_order_terms() -> Vec<(usize, Gate)> {
        let z = Fr::zero();
        let o = Fr::one();
        (0..2081)
            .map(|index| {
                match index {
                    0..=1023 => (index, gate(index, index, z, -o, z, o)),
                    1024..=1342 => {
                        let reserved = index - 1024;
                        let wire = if reserved < 159 {
                            97 + reserved
                        } else {
                            352 + reserved - 159
                        };
                        (index, gate(wire, 0, z, o, z, z))
                    }
                    1343 => (1343, gate(576, 0, z, o, z, z)),
                    1344..=1790 => (index, gate(577 + index - 1344, 0, z, o, z, z)),
                    1791..=1792 => (index, gate(31 + 256 * (index - 1791), 0, z, o, z, z)),
                    1793..=1824 => {
                        let bit = index - 1793;
                        let binary_weight = Fr::from(1u64 << bit);
                        (
                            1793,
                            gate(
                                256 + bit,
                                bit,
                                if bit == 0 { -o } else { z },
                                binary_weight,
                                -binary_weight,
                                z,
                            ),
                        )
                    }
                    1825..=2016 => {
                        let component = (index - 1825) / 64;
                        let bit = (index - 1825) % 64;
                        let unsigned_weight = Fr::from(1u64 << bit);
                        // Native timestamps are signed i64; delta is unsigned.
                        let signed_weight = if bit == 63 {
                            -unsigned_weight
                        } else {
                            unsigned_weight
                        };
                        let (wire, weight) = match component {
                            0 => (288 + bit, signed_weight),
                            1 => (32 + bit, -signed_weight),
                            _ => (512 + bit, -unsigned_weight),
                        };
                        let unit = if index == 1825 { o } else { z };
                        // (1-first) * (current-previous-delta-1).
                        (1794, gate(wire, 96, -unit, weight, unit, -weight))
                    }
                    _ => {
                        let bit = index - 2017;
                        (1795 + bit, gate(512 + bit, 96, z, z, z, o))
                    }
                }
            })
            .collect()
    }

    fn reference_gates(n: u64, tip_time: i64) -> Vec<(usize, Gate)> {
        let order = reference_order_terms();
        let mut start = [0u8; 32];
        start[12] = 1;
        let mut tip = [0u8; 32];
        tip[..4].copy_from_slice(&(n as u32).to_le_bytes());
        tip[4..12].copy_from_slice(&tip_time.to_le_bytes());
        let mut expected =
            Vec::with_capacity(ORDER_TERM_COUNT * n as usize + METADATA_BITS * (n as usize + 1));
        for owner in 0..n as usize {
            let row_base = owner << LOCAL_ROW_LOG;
            let input_base = owner << LOCAL_INPUT_LOG;
            for (row, term) in &order {
                expected.push((
                    row_base + row,
                    Gate {
                        left: input_base + ORDER_OFFSET + term.left,
                        right: input_base + ORDER_OFFSET + term.right,
                        c0: term.c0,
                        c1: term.c1,
                        c2: term.c2,
                        c3: term.c3,
                    },
                ));
            }
            if owner == 0 {
                for bit in 0..METADATA_BITS {
                    expected.push((
                        row_base + METADATA_FAMILY_BASE + bit,
                        gate(
                            input_base + ORDER_OFFSET + bit,
                            0,
                            -endpoint_bit(&start, bit),
                            Fr::one(),
                            Fr::zero(),
                            Fr::zero(),
                        ),
                    ));
                }
            }
            if owner > 0 {
                for bit in 0..METADATA_BITS {
                    expected.push((
                        row_base + METADATA_FAMILY_BASE + bit,
                        gate(
                            ((owner - 1) << LOCAL_INPUT_LOG) + ORDER_OFFSET + METADATA_BITS + bit,
                            input_base + ORDER_OFFSET + bit,
                            Fr::zero(),
                            Fr::one(),
                            -Fr::one(),
                            Fr::zero(),
                        ),
                    ));
                }
            }
            if owner + 1 == n as usize {
                for bit in 0..METADATA_BITS {
                    expected.push((
                        row_base + METADATA_FAMILY_BASE + METADATA_BITS + bit,
                        gate(
                            input_base + ORDER_OFFSET + METADATA_BITS + bit,
                            0,
                            -endpoint_bit(&tip, bit),
                            Fr::one(),
                            Fr::zero(),
                            Fr::zero(),
                        ),
                    ));
                }
            }
        }
        expected
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

    fn collect(layout: &HeaderMetadataOrderLayout) -> Vec<(usize, Gate)> {
        let mut gates = Vec::with_capacity(layout.term_count);
        for slot in 0..layout.n {
            layout
                .visit_slot_terms(slot, |row, gate| {
                    gates.push((row, gate));
                    Ok(())
                })
                .unwrap();
        }
        gates
    }

    #[test]
    fn n3_last_link_and_padding_independent_oracle() {
        let layout = HeaderMetadataOrderLayout::compile(3, 2, -5).unwrap();
        let local_terms: Vec<_> = layout
            .order
            .circuit
            .terms
            .iter()
            .map(|term| (term.row, term.gate.clone()))
            .collect();
        assert_eq!(local_terms, reference_order_terms());
        let emitted = collect(&layout);
        let reference = reference_gates(3, -5);
        assert_eq!(layout.term_count(), 2_337 * 3 + 256);
        assert_eq!(emitted, reference);

        let r = dense_point(layout.row_log, 11);
        let u = dense_point(layout.input_log, 19);
        let v = dense_point(layout.input_log, 31);
        let expected = direct_coefficients(&reference, &r, &u, &v);
        assert!(expected.iter().any(|coefficient| !coefficient.is_zero()));
        assert_eq!(layout.coefficients(&r, &u, &v).unwrap(), expected);
        let last_link = reference
            .iter()
            .position(|(row, gate)| {
                *row == (2usize << LOCAL_ROW_LOG) + METADATA_FAMILY_BASE + 255
                    && gate.c2 == -Fr::one()
            })
            .unwrap();
        for fault in 0..6 {
            let mut mutant = reference.clone();
            match fault {
                0 => {
                    mutant.remove(last_link);
                }
                1 => {
                    mutant[last_link].0 -= 1 << LOCAL_ROW_LOG;
                }
                2 => {
                    let g = &mut mutant[last_link].1;
                    std::mem::swap(&mut g.left, &mut g.right);
                }
                3 => {
                    mutant[last_link].1.left += 1 << LOCAL_INPUT_LOG;
                }
                4 => {
                    mutant[last_link].0 ^= 1 << FAMILY_BIT;
                }
                _ => {
                    mutant.last_mut().unwrap().1.right = (2usize << LOCAL_INPUT_LOG) + ORDER_OFFSET;
                }
            }
            assert_ne!(
                direct_coefficients(&mutant, &r, &u, &v),
                expected,
                "single relation mutant{fault}"
            );
        }

        let owner = 2usize;
        let row = (owner << LOCAL_ROW_LOG) + METADATA_FAMILY_BASE + 255;
        let left = ((owner - 1) << LOCAL_INPUT_LOG) + ORDER_OFFSET + METADATA_BITS + 255;
        let right = (owner << LOCAL_INPUT_LOG) + ORDER_OFFSET + 255;
        let r = bool_point(row, layout.row_log);
        let u = bool_point(left, layout.input_log);
        let v = bool_point(right, layout.input_log);
        assert_eq!(
            layout.coefficients(&r, &u, &v).unwrap(),
            [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
        );

        let reversed = layout
            .coefficients(
                &r,
                &bool_point(right, layout.input_log),
                &bool_point(left, layout.input_log),
            )
            .unwrap();
        assert_eq!(reversed, [Fr::zero(); 4]);

        let order_row = 0usize;
        let order_wire = ORDER_OFFSET;
        let r = bool_point(order_row, layout.row_log);
        let u = bool_point(order_wire, layout.input_log);
        let v = bool_point(order_wire, layout.input_log);
        assert_eq!(
            layout.coefficients(&r, &u, &v).unwrap(),
            [Fr::zero(), -Fr::one(), Fr::zero(), Fr::one()]
        );
        let wrong_bank = ORDER_OFFSET + (1 << ORDER_INPUT_LOG);
        assert_eq!(
            layout
                .coefficients(&r, &bool_point(wrong_bank, layout.input_log), &v)
                .unwrap(),
            [Fr::zero(); 4],
        );

        let terminal_row = (2usize << LOCAL_ROW_LOG) + METADATA_FAMILY_BASE + METADATA_BITS;
        let terminal_left = (2usize << LOCAL_INPUT_LOG) + ORDER_OFFSET + METADATA_BITS;
        let r = bool_point(terminal_row, layout.row_log);
        let u = bool_point(terminal_left, layout.input_log);
        let global_zero_v = vec![Fr::zero(); layout.input_log];
        assert_eq!(
            layout.coefficients(&r, &u, &global_zero_v).unwrap(),
            [-Fr::one(), Fr::one(), Fr::zero(), Fr::zero()]
        );
        let local_zero_v = bool_point((2usize << LOCAL_INPUT_LOG) + ORDER_OFFSET, layout.input_log);
        assert_eq!(
            layout.coefficients(&r, &u, &local_zero_v).unwrap(),
            [Fr::zero(); 4]
        );

        let noncanonical_member = (2usize << LOCAL_ROW_LOG) + METADATA_FAMILY_BASE + 1024 + 255;
        let r = bool_point(noncanonical_member, layout.row_log);
        let left = (1usize << LOCAL_INPUT_LOG) + ORDER_OFFSET + METADATA_BITS + 255;
        let right = (2usize << LOCAL_INPUT_LOG) + ORDER_OFFSET + 255;
        assert_eq!(
            layout
                .coefficients(
                    &r,
                    &bool_point(left, layout.input_log),
                    &bool_point(right, layout.input_log)
                )
                .unwrap(),
            [Fr::zero(); 4]
        );

        let padded_row = (3usize << LOCAL_ROW_LOG) + METADATA_FAMILY_BASE + 255;
        let r = bool_point(padded_row, layout.row_log);
        let u = bool_point(
            (3usize << LOCAL_INPUT_LOG) + ORDER_OFFSET + 255,
            layout.input_log,
        );
        let v = bool_point(
            (3usize << LOCAL_INPUT_LOG) + ORDER_OFFSET + 255,
            layout.input_log,
        );
        assert_eq!(layout.coefficients(&r, &u, &v).unwrap(), [Fr::zero(); 4]);
    }

    fn bank(
        current_height: u32,
        current_time: i64,
        previous_height: u32,
        previous_time: i64,
        first: bool,
    ) -> Vec<Fr> {
        header_order::witness(
            current_height,
            current_time,
            previous_height,
            previous_time,
            first,
        )
        .unwrap()
        .into_iter()
        .map(|bit| Fr::from(bit as u64))
        .collect()
    }

    fn sparse_input_value(banks: &[Vec<Fr>], wire: usize) -> Fr {
        if wire == 0 {
            return Fr::zero();
        }
        let owner = wire >> LOCAL_INPUT_LOG;
        let local = wire & (LOCAL_INPUT_WIDTH - 1);
        if local < ORDER_OFFSET || local >= ORDER_OFFSET + (1 << ORDER_INPUT_LOG) {
            return Fr::zero();
        }
        banks[owner][local - ORDER_OFFSET]
    }

    fn row_residuals(
        gates: &[(usize, Gate)],
        banks: &[Vec<Fr>],
        family: usize,
        width: usize,
    ) -> Vec<Fr> {
        let mut rows = vec![Fr::zero(); width];
        for (row, gate) in gates {
            if (*row >> FAMILY_BIT) & 1 != family {
                continue;
            }
            let a = sparse_input_value(banks, gate.left);
            let b = sparse_input_value(banks, gate.right);
            rows[*row] += gate.c0 + gate.c1 * a + gate.c2 * b + gate.c3 * a * b;
        }
        rows
    }

    fn local_order_rows(banks: &[Vec<Fr>]) -> Vec<Vec<Fr>> {
        let order = header_order::local_order().unwrap();
        banks
            .iter()
            .map(|bank| {
                let mut rows = vec![Fr::zero(); order.circuit.row_count];
                for term in &order.circuit.terms {
                    let a = bank[term.gate.left];
                    let b = bank[term.gate.right];
                    rows[term.row] +=
                        term.gate.c0 + term.gate.c1 * a + term.gate.c2 * b + term.gate.c3 * a * b;
                }
                rows
            })
            .collect()
    }

    #[test]
    fn stale_previous_timestamp_delta_recomputed_keeps_local_order_but_breaks_link() {
        let layout = HeaderMetadataOrderLayout::compile(3, 2, 3000).unwrap();
        let valid = vec![
            bank(1, 1000, 0, 0, true),
            bank(2, 2000, 1, 1000, false),
            bank(3, 3000, 2, 2000, false),
        ];
        let stale = vec![
            valid[0].clone(),
            bank(2, 2000, 1, 1001, false),
            valid[2].clone(),
        ];
        assert!(local_order_rows(&valid).iter().flatten().all(Zero::is_zero));
        assert!(local_order_rows(&stale).iter().flatten().all(Zero::is_zero));

        let expected = reference_gates(3, 3000);
        let emitted = collect(&layout);
        assert_eq!(emitted, expected);
        assert!(row_residuals(&emitted, &valid, 0, layout.row_count)
            .iter()
            .all(Zero::is_zero));
        assert!(row_residuals(&emitted, &stale, 0, layout.row_count)
            .iter()
            .all(Zero::is_zero));
        let valid_rows = row_residuals(&emitted, &valid, 1, layout.row_count);
        assert!(valid_rows.iter().all(Zero::is_zero));
        let stale_rows = row_residuals(&emitted, &stale, 1, layout.row_count);
        let failures: Vec<_> = stale_rows
            .iter()
            .enumerate()
            .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
            .collect();
        assert_eq!(
            failures,
            vec![(1usize << LOCAL_ROW_LOG) + METADATA_FAMILY_BASE + 32]
        );
        assert!(row_residuals(&expected, &valid, 1, layout.row_count)
            .iter()
            .all(Zero::is_zero));
        assert!(row_residuals(&expected, &stale, 1, layout.row_count)
            .iter()
            .any(|value| !value.is_zero()));
    }

    #[test]
    fn n1_n5_bounds_dimensions_and_zero_sink_faults() {
        let one = HeaderMetadataOrderLayout::compile(1, 0, i64::MIN).unwrap();
        assert_eq!(one.input_log(), 20);
        assert_eq!(one.row_log(), 12);
        assert_eq!(one.term_count(), 2_337 + 256);
        assert_eq!(collect(&one).len(), one.term_count());

        let zero_v = vec![Fr::zero(); one.input_log];
        let first_anchor = one
            .coefficients(
                &bool_point(METADATA_FAMILY_BASE + 96, one.row_log),
                &bool_point(ORDER_OFFSET + 96, one.input_log),
                &zero_v,
            )
            .unwrap();
        assert_eq!(
            first_anchor,
            [-Fr::one(), Fr::one(), Fr::zero(), Fr::zero()]
        );
        let terminal_anchor = one
            .coefficients(
                &bool_point(METADATA_FAMILY_BASE + METADATA_BITS, one.row_log),
                &bool_point(ORDER_OFFSET + METADATA_BITS, one.input_log),
                &zero_v,
            )
            .unwrap();
        assert_eq!(
            terminal_anchor,
            [-Fr::one(), Fr::one(), Fr::zero(), Fr::zero()]
        );

        let five = HeaderMetadataOrderLayout::compile(5, 3, -987).unwrap();
        assert_eq!(five.term_count(), 2_337 * 5 + 256);
        assert_eq!(collect(&five).len(), five.term_count());
        let owner = 4usize;
        let link = five
            .coefficients(
                &bool_point(
                    (owner << LOCAL_ROW_LOG) + METADATA_FAMILY_BASE,
                    five.row_log,
                ),
                &bool_point(
                    ((owner - 1) << LOCAL_INPUT_LOG) + ORDER_OFFSET + METADATA_BITS,
                    five.input_log,
                ),
                &bool_point((owner << LOCAL_INPUT_LOG) + ORDER_OFFSET, five.input_log),
            )
            .unwrap();
        assert_eq!(link, [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]);
        let padded_owner = 7usize;
        assert_eq!(
            five.coefficients(
                &bool_point(
                    (padded_owner << LOCAL_ROW_LOG) + METADATA_FAMILY_BASE,
                    five.row_log
                ),
                &bool_point(
                    (padded_owner << LOCAL_INPUT_LOG) + ORDER_OFFSET + METADATA_BITS,
                    five.input_log
                ),
                &bool_point(
                    (padded_owner << LOCAL_INPUT_LOG) + ORDER_OFFSET,
                    five.input_log
                ),
            )
            .unwrap(),
            [Fr::zero(); 4],
        );
        let mut calls = 0;
        assert!(five
            .visit_slot_terms(5, |_, _| {
                calls += 1;
                Ok(())
            })
            .is_err());
        assert_eq!(calls, 0);

        let point_r = vec![Fr::zero(); five.row_log];
        let point_u = vec![Fr::zero(); five.input_log];
        let point_v = vec![Fr::zero(); five.input_log];
        assert!(five
            .coefficients(&point_r[..point_r.len() - 1], &point_u, &point_v)
            .is_err());
        let mut long_r = point_r.clone();
        long_r.push(Fr::zero());
        assert!(five.coefficients(&long_r, &point_u, &point_v).is_err());
        assert!(five
            .coefficients(&point_r, &point_u[..point_u.len() - 1], &point_v)
            .is_err());
        let mut long_u = point_u.clone();
        long_u.push(Fr::zero());
        assert!(five.coefficients(&point_r, &long_u, &point_v).is_err());
        assert!(five
            .coefficients(&point_r, &point_u, &point_v[..point_v.len() - 1])
            .is_err());
        let mut long_v = point_v.clone();
        long_v.push(Fr::zero());
        assert!(five.coefficients(&point_r, &point_u, &long_v).is_err());
        assert!(HeaderMetadataOrderLayout::compile(0, 2, 0).is_err());
        assert!(HeaderMetadataOrderLayout::compile(5, 2, 0).is_err());
        assert!(HeaderMetadataOrderLayout::compile(1, 22, 0).is_err());
    }

    #[test]
    fn symbolic_h21_active_endpoint_and_padded_owner() {
        let n = (1u64 << MAX_SLOT_LOG) - 1;
        let layout = HeaderMetadataOrderLayout::compile(n, MAX_SLOT_LOG, -1).unwrap();
        assert_eq!(layout.input_log(), 41);
        assert_eq!(layout.row_log(), 33);
        assert_eq!(
            layout.term_count(),
            (n as usize) * TERMS_PER_OWNER + METADATA_BITS
        );

        let active_owner = n as usize - 1;
        let active_row = active_owner << LOCAL_ROW_LOG;
        let active_wire = (active_owner << LOCAL_INPUT_LOG) + ORDER_OFFSET;
        let r = bool_point(active_row, layout.row_log);
        let u = bool_point(active_wire, layout.input_log);
        let v = bool_point(active_wire, layout.input_log);
        assert_eq!(
            layout.coefficients(&r, &u, &v).unwrap(),
            [Fr::zero(), -Fr::one(), Fr::zero(), Fr::one()]
        );

        let link_row = (active_owner << LOCAL_ROW_LOG) + METADATA_FAMILY_BASE + 255;
        let link_left =
            ((active_owner - 1) << LOCAL_INPUT_LOG) + ORDER_OFFSET + METADATA_BITS + 255;
        let link_right = (active_owner << LOCAL_INPUT_LOG) + ORDER_OFFSET + 255;
        assert_eq!(
            layout
                .coefficients(
                    &bool_point(link_row, layout.row_log),
                    &bool_point(link_left, layout.input_log),
                    &bool_point(link_right, layout.input_log),
                )
                .unwrap(),
            [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()],
        );

        let terminal_row = (active_owner << LOCAL_ROW_LOG) + METADATA_FAMILY_BASE + METADATA_BITS;
        let terminal_left = (active_owner << LOCAL_INPUT_LOG) + ORDER_OFFSET + METADATA_BITS;
        assert_eq!(
            layout
                .coefficients(
                    &bool_point(terminal_row, layout.row_log),
                    &bool_point(terminal_left, layout.input_log),
                    &vec![Fr::zero(); layout.input_log],
                )
                .unwrap(),
            [-Fr::one(), Fr::one(), Fr::zero(), Fr::zero()],
        );

        let padded_owner = (1usize << MAX_SLOT_LOG) - 1;
        let r = bool_point(padded_owner << LOCAL_ROW_LOG, layout.row_log);
        let u = bool_point(
            (padded_owner << LOCAL_INPUT_LOG) + ORDER_OFFSET,
            layout.input_log,
        );
        let v = u.clone();
        assert_eq!(layout.coefficients(&r, &u, &v).unwrap(), [Fr::zero(); 4]);
    }

    #[test]
    fn descriptor_binding_replays_and_separates_owner_domain_and_tip_time() {
        fn challenge(layout: &HeaderMetadataOrderLayout) -> Fr {
            let mut transcript = Transcript::new(b"metadata-order-binding-test");
            layout.bind(&mut transcript);
            transcript.challenge_scalar(b"first-after-binding")
        }
        let base = HeaderMetadataOrderLayout::compile(3, 2, 42).unwrap();
        assert_eq!(
            challenge(&base),
            challenge(&HeaderMetadataOrderLayout::compile(3, 2, 42).unwrap())
        );
        assert_ne!(
            challenge(&base),
            challenge(&HeaderMetadataOrderLayout::compile(3, 3, 42).unwrap())
        );
        assert_ne!(
            challenge(&base),
            challenge(&HeaderMetadataOrderLayout::compile(4, 2, 42).unwrap())
        );
        assert_ne!(
            challenge(&base),
            challenge(&HeaderMetadataOrderLayout::compile(3, 2, 43).unwrap())
        );
        let baseline = challenge(&base);
        for field in 0..9 {
            let mut fault = HeaderMetadataOrderLayout::compile(3, 2, 42).unwrap();
            match field {
                0 => fault.n += 1,
                1 => fault.slot_log += 1,
                2 => fault.input_log += 1,
                3 => fault.row_log += 1,
                4 => fault.input_len += 1,
                5 => fault.row_count += 1,
                6 => fault.term_count += 1,
                7 => fault.order_shape.copies += 1,
                _ => fault.order_fingerprint.push('0'),
            }
            assert_ne!(challenge(&fault), baseline, "bound field{field}");
        }
        for identity in 0..34 {
            let mut t = Transcript::new(b"metadata-order-binding-test");
            let mut genesis = header_order::MAINNET_GENESIS;
            let mut profile = PROFILE;
            let mut version = VERSION;
            if identity < 32 {
                genesis[identity] ^= 1;
            } else if identity == 32 {
                profile = b"different-composite-profile";
            } else {
                version += 1;
            }
            base.bind_with_identity(&mut t, profile, version, &genesis);
            assert_ne!(
                t.challenge_scalar(b"first-after-binding"),
                baseline,
                "identity{identity}"
            );
        }
    }

    #[test]
    fn both_families_prevalidated_before_any_external_sink() {
        for field in 0..7 {
            let mut fault = HeaderMetadataOrderLayout::compile(3, 2, 3000).unwrap();
            match field {
                0 => fault.input_len = (2usize << LOCAL_INPUT_LOG) + LOCAL_INPUT_WIDTH - 1,
                1 => fault.row_count = (2usize << LOCAL_ROW_LOG) + LOCAL_ROW_WIDTH - 1,
                2 => fault.order.circuit.terms.last_mut().unwrap().row = 1 << ORDER_ROW_LOG,
                3 => fault.order.circuit.terms.last_mut().unwrap().gate.left = 1 << ORDER_INPUT_LOG,
                4 => {
                    fault.order.circuit.terms.last_mut().unwrap().gate.right = 1 << ORDER_INPUT_LOG
                }
                5 => fault.metadata = HeaderAdjacencyLayout::compile_metadata(4, 2, 3000).unwrap(),
                _ => fault.metadata = HeaderAdjacencyLayout::compile_metadata(2, 1, 3000).unwrap(),
            }
            let mut calls = 0;
            assert!(
                fault
                    .visit_slot_terms(2, |_, _| {
                        calls += 1;
                        Ok(())
                    })
                    .is_err(),
                "field{field}"
            );
            assert_eq!(calls, 0, "partial emission before fault{field}");
        }
        let valid = HeaderMetadataOrderLayout::compile(3, 2, 3000).unwrap();
        let mut calls = 0;
        assert!(valid
            .visit_slot_terms(2, |_, _| {
                calls += 1;
                Err("sink stopped".into())
            })
            .is_err());
        assert_eq!(calls, 1);
    }
}
