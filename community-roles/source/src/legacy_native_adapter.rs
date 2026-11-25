//! Bounded native packed-row diagnostic. Foreign reads are candidate inputs,
//! not authenticated commitment openings. The cap is consumer-owned e64.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalSerialize;
use num_bigint::{BigInt, BigUint};
use num_traits::One as NumOne;
use std::collections::BTreeMap;
use crate::{
    daa_history_roster::{DaaHistoryRoster, BANKS},
    legacy_envelope_map::{Map, Inputs, BASE, BANK, D_LOCAL, T_LOCAL},
    native_owner_exports::NativeExports,
    packed_owner_assembly::{NativePrefix, NativePackedRow, validate_native_plan_input},
    sparse::Term, transcript::Transcript,
    work_tree_history_plan::WorkTreeHistoryPlan, work_tree_layout::WIDTH,
};

const HEADERS: usize = 3073;
const E: usize = 64;
const CONTRACT: &[u8] = b"1AC18112EC82D0E770D6501EACA59A15194EAA1BE756CADBC8F9312E8EE9EDE6";

pub(crate) struct CapSummary {
    pub(crate) maximum: BigUint,
    pub(crate) height: usize,
    pub(crate) total: BigUint,
}

/// This scalar gate precedes assignment templates and owner rows. It does not
/// authenticate RAW or adopt a protocol envelope.
pub(crate) fn native_cap_summary(input: &NativePrefix) -> Result<CapSummary, String> {
    if input.header_count() != HEADERS { return Err("legacy native cap requires N3073".into()); }
    let cap = BigUint::one() << E;
    let mut summary = CapSummary { maximum: BigUint::zero(), height: 0, total: BigUint::zero() };
    for height in 2..=HEADERS {
        let d = crate::work_tree_work::native_decode(input.compact_n_bits(height)?)?;
        if d.is_zero() || d > cap { return Err(format!("legacy native e64 cap failed at height{height}")); }
        if d > summary.maximum { summary.maximum = d.clone(); summary.height = height; }
        summary.total += d;
    }
    if summary.total != BigUint::from_bytes_be(&input.total_be28()) {
        return Err("legacy native decoded total mismatch".into());
    }
    Ok(summary)
}

pub(crate) struct LegacyNativeAdapter<'a> {
    parent: &'a WorkTreeHistoryPlan,
    input: &'a NativePrefix,
    roster: DaaHistoryRoster<'a>,
    exports: NativeExports<'a>,
    map: Map,
    binding: [u8;32],
}

impl<'a> LegacyNativeAdapter<'a> {
    pub(crate) fn compile(parent: &'a WorkTreeHistoryPlan, input: &'a NativePrefix) -> Result<Self, String> {
        Self::compile_e(parent, input, E)
    }
    fn compile_e(parent: &'a WorkTreeHistoryPlan, input: &'a NativePrefix, e: usize) -> Result<Self, String> {
        if e != E { return Err("legacy native diagnostic cap requires e64".into()); }
        if parent.headers() != HEADERS as u64 || parent.slot_log() != 12 || parent.slots() != 4096 {
            return Err("legacy native adapter requires N3073/S12".into());
        }
        native_cap_summary(input)?;
        validate_native_plan_input(parent, input)?;
        Self::certify_bank(parent)?;
        let map = Map::from_parent(parent, e)?;
        let roster = DaaHistoryRoster::compile(parent)?;
        let exports = NativeExports::new_for_history(parent, input)?;
        let mut result = Self { parent, input, roster, exports, map, binding: [0;32] };
        let mut t = Transcript::new(b"legacy-native-local-adapter-binding");
        result.bind(&mut t);
        let mut bytes = Vec::new();
        t.challenge_scalar(b"binding").serialize_compressed(&mut bytes)
            .map_err(|e| format!("legacy native binding serialization: {e}"))?;
        if bytes.len() != 32 { return Err("legacy native binding width".into()); }
        result.binding.copy_from_slice(&bytes);
        Ok(result)
    }
    fn certify_bank(parent: &WorkTreeHistoryPlan) -> Result<(), String> {
        let source = parent.header_boundary().canonical_circuit();
        if source.input_len != WIDTH || source.row_count != 1<<19 || BASE+BANK != 663552
            || BANKS.iter().any(|&(lo,hi)| lo < BASE+BANK && BASE < hi) {
            return Err("legacy native bank geometry changed".into());
        }
        for term in &source.terms {
            let g = &term.gate;
            let left_read = !g.c1.is_zero() || !g.c3.is_zero();
            let right_read = !g.c2.is_zero() || !g.c3.is_zero();
            if (left_read && (BASE..BASE+BANK).contains(&g.left))
                || (right_read && (BASE..BASE+BANK).contains(&g.right)) {
                return Err("legacy native bank still read by HEADER".into());
            }
        }
        let mask = parent.physical_assignment_replacement_mask(0)?;
        if mask[BASE..BASE+BANK].iter().any(|b| *b) {
            return Err("legacy native bank parent permission changed".into());
        }
        Ok(())
    }
    fn bind(&self, t: &mut Transcript) {
        self.parent.bind(t);
        self.roster.bind(t);
        t.append_bytes(b"legacy-native-map-contract", CONTRACT);
        for (label, value) in [
            (b"legacy-native-n".as_slice(), self.parent.headers()),
            (b"legacy-native-h", self.parent.slot_log() as u64),
            (b"legacy-native-slots", self.parent.slots() as u64),
            (b"legacy-native-leaves", self.parent.descriptor().leaves as u64),
            (b"legacy-native-genuine", self.parent.descriptor().genuine as u64),
            (b"legacy-native-input-log", 20+self.parent.slot_log() as u64),
            (b"legacy-native-map-row-log", 14+self.parent.slot_log() as u64),
            (b"legacy-native-bank", BASE as u64), (b"legacy-native-bank-bits", BANK as u64),
            (b"legacy-native-D", D_LOCAL as u64), (b"legacy-native-D-bits", 224),
            (b"legacy-native-time", T_LOCAL as u64), (b"legacy-native-time-bits", 64),
            (b"legacy-native-anchor-height-low", 960), (b"legacy-native-header-owner-low", 959),
            (b"legacy-native-work-owner-low", 958), (b"legacy-native-epoch", 1024),
            (b"legacy-native-offset", 64), (b"legacy-native-schedule-cap", 843776),
            (b"legacy-native-excluded-q", 407), (b"legacy-native-e", E as u64),
        ] { t.append_u64(label, value); }
        // 2^64 is an integer constant, never cast to u64.
        t.append_bytes(b"legacy-native-U-convention", b"diagnostic-U=integer-2^e;e<=64;not-protocol-U");
        t.append_bytes(b"legacy-native-row-convention", b"row=owner*2^14+local;linear-right=owner*2^20;Boolean=joint-diagonal");
    }
    pub(crate) fn check(&self, parent: &WorkTreeHistoryPlan, input: &NativePrefix) -> Result<(), String> {
        if !std::ptr::eq(parent,self.parent) || !std::ptr::eq(input,self.input)
            || parent.headers()!=HEADERS as u64 || parent.slot_log()!=12 || parent.slots()!=4096
            || parent.descriptor().root!=input.root() || parent.work_profile().total_be28!=input.total_be28()
            || self.map.binding().e!=E || self.map.binding().parent_root!=Some(parent.descriptor().root) {
            return Err("legacy native adapter identity mismatch".into());
        }
        Ok(())
    }
    pub(crate) fn parent(&self) -> &'a WorkTreeHistoryPlan { self.parent }
    pub(crate) fn input(&self) -> &'a NativePrefix { self.input }
    pub(crate) fn roster(&self) -> &DaaHistoryRoster<'a> { &self.roster }
    pub(crate) fn binding(&self) -> [u8;32] { self.binding }
    pub(crate) fn export_bit(&self, index: usize) -> Result<bool,String> { self.exports.bit(index) }
    pub(crate) fn extend_mask(&self, owner: usize, mut mask: Vec<bool>) -> Result<Vec<bool>,String> {
        self.check(self.parent,self.input)?;
        let expected = self.parent.physical_assignment_replacement_mask(owner as u64)?;
        if mask != expected { return Err("legacy native parent mask identity mismatch".into()); }
        for (lo,hi) in self.map.active_intervals(owner as u64)? {
            if lo < BASE || hi > BASE+BANK || lo >= hi {
                return Err("legacy native active field range".into());
            }
            mask[lo..hi].fill(true);
        }
        Ok(mask)
    }
    fn assigned_inputs(&self, owner: usize) -> Result<Inputs,String> {
        let mut inputs = Inputs::default();
        for imp in self.map.imports(owner as u64)? {
            let mut n = BigInt::from(0);
            for bit in 0..imp.width {
                if self.exports.bit(self.map.input_index(imp,bit)?)? { n += BigInt::from(1)<<bit; }
            }
            inputs.put(&self.map,imp,&n)?;
        }
        Ok(inputs)
    }
    pub(crate) fn helpers(&self, owner: usize) -> Result<Vec<bool>,String> {
        self.check(self.parent,self.input)?;
        Ok(self.map.generate(owner as u64,&self.assigned_inputs(owner)?)?.bits)
    }
    pub(crate) fn terms(&self, owner: usize) -> Result<Vec<Term>,String> {
        self.check(self.parent,self.input)?;
        self.map.terms(owner as u64)
    }
    /// Component comparator: reads own cells from packed bytes and foreign
    /// fields from the candidate reader. It supplies no foreign authentication.
    fn map_failures(
        &self, owner: usize, row: &NativePackedRow,
        mut read_bit: impl FnMut(usize)->Result<bool,String>,
    ) -> Result<Vec<(usize,Fr)>,String> {
        self.check(self.parent,self.input)?;
        row.admit_legacy_for_test(self,owner)?;
        let imports = self.map.imports(owner as u64)?;
        let terms = self.terms(owner)?;
        let mut cache = BTreeMap::<usize,bool>::new();
        let mut value = |index:usize| -> Result<Fr,String> {
            if index >= self.parent.slots()*WIDTH { return Err("LegacyMap input outside domain".into()); }
            let source_owner=index/WIDTH; let local=index%WIDTH;
            let bit = if source_owner==owner { packed_bit(row.packed_bytes(),local) }
            else {
                if !imports.iter().any(|imp| imp.owner==source_owner as u64
                    && imp.local<=local && local<imp.local+imp.width) {
                    return Err("LegacyMap foreign coordinate outside typed imports".into());
                }
                if let Some(&bit)=cache.get(&index) { bit } else {
                    let bit=read_bit(index)?; cache.insert(index,bit); bit
                }
            };
            Ok(Fr::from(bit as u64))
        };
        let mut sums=BTreeMap::<usize,Fr>::new();
        for term in terms {
            let g=term.gate; let mut z=g.c0;
            if !g.c1.is_zero() { z+=g.c1*value(g.left)?; }
            if !g.c2.is_zero() { z+=g.c2*value(g.right)?; }
            if !g.c3.is_zero() { z+=g.c3*value(g.left)?*value(g.right)?; }
            *sums.entry(term.row).or_insert(Fr::zero())+=z;
        }
        Ok(sums.into_iter().filter(|(_,z)| !z.is_zero()).collect())
    }
}

fn packed_bit(bytes:&[u8], wire:usize)->bool { bytes[wire/8] & (1<<(wire%8)) != 0 }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::legacy_envelope_map::{Kind, RATIO, SMAX};
    use crate::packed_owner_assembly::{self as assembly, NativeOwnerProducer, AssemblyFault};
    use crate::packed_owner_assembly_tests as fixtures;
    use num_traits::ToPrimitive;

    fn checked_fixture()->(&'static NativePrefix,&'static WorkTreeHistoryPlan) {
        let input=fixtures::legacy_prefix_for_test();
        // Every separately selected libtest process reaches this before plan or templates.
        let cap=native_cap_summary(input).unwrap();
        assert_eq!(cap.maximum,BigUint::from(185435213004800u64));
        assert_eq!(cap.height,3073);
        assert_eq!(cap.total,BigUint::from(24293759260819456u64));
        assert_eq!((&cap.maximum-BigUint::one()).bits(),48);
        assert_eq!(E,64);
        (input,fixtures::legacy_assembly_plan_for_test())
    }
    fn error<T>(value:Result<T,String>)->String {
        match value {Err(e)=>e,Ok(_)=>panic!("negative accepted")}
    }
    fn residual_rows(failures:Vec<(usize,Fr)>,owner:usize)->Vec<usize> {
        failures.into_iter().map(|(row,_)|row-owner*(1<<14)).collect()
    }
    fn import_bits_from_packed(
        adapter:&LegacyNativeAdapter<'_>, producer:&NativeOwnerProducer<'_>, owner:usize,
    )->BTreeMap<usize,bool> {
        let mut by_owner=BTreeMap::<usize,Vec<crate::legacy_envelope_map::Import>>::new();
        for imp in adapter.map.imports(owner as u64).unwrap() {
            if imp.owner!=owner as u64 { by_owner.entry(imp.owner as usize).or_default().push(imp); }
        }
        let mut bits=BTreeMap::new();
        for (source,imports) in by_owner {
            let row=producer.produce(source).unwrap();
            for imp in imports { for bit in 0..imp.width {
                let index=adapter.map.input_index(imp,bit).unwrap();
                let actual=packed_bit(row.packed_bytes(),imp.local+bit);
                assert_eq!(adapter.export_bit(index).unwrap(),actual,"typed source packed port");
                bits.insert(index,actual);
            }}
        }
        bits
    }

    #[test]
    fn header_claims_and_selected_native_rows() {
        let (input,plan)=checked_fixture();
        LegacyNativeAdapter::certify_bank(plan).unwrap();
        let adapter=LegacyNativeAdapter::compile(plan,input).unwrap();
        let producer=NativeOwnerProducer::new_for_legacy_history(plan,input,&adapter).unwrap();
        let old=NativeOwnerProducer::new(plan,input).unwrap();
        let helpers=adapter.helpers(3007).unwrap();
        let first=helpers.iter().position(|bit|*bit).unwrap();
        assert_eq!(error(assembly::legacy_old_seeder_conflict_for_test(&old,&adapter,3007)),
            format!("claim conflict owner3007 wire{}",BASE+first));
        for owner in [0usize,959,1983,3007,3072,4095] {
            let parent_mask=plan.physical_assignment_replacement_mask(owner as u64).unwrap();
            let active=adapter.map.active_intervals(owner as u64).unwrap();
            let mask=adapter.extend_mask(owner,parent_mask.clone()).unwrap();
            for wire in 0..WIDTH {
                assert_eq!(mask[wire],parent_mask[wire] || active.iter().any(|&(a,b)|a<=wire && wire<b));
            }
            assert_eq!(mask[BASE-1],parent_mask[BASE-1]);
            assert_eq!(mask[BASE+BANK],parent_mask[BASE+BANK]);
            let row=producer.produce(owner).unwrap();
            let legacy_seeder=producer.produce_legacy_header_for_test(owner).unwrap();
            assert_eq!(row.packed_bytes(),legacy_seeder.packed_bytes());
            let helpers=adapter.helpers(owner).unwrap();
            for (i,&bit) in helpers.iter().enumerate() {
                assert_eq!(packed_bit(row.packed_bytes(),BASE+i),bit);
                if !active.iter().any(|&(a,b)|a<=BASE+i && BASE+i<b) { assert!(!bit); }
            }
            let receipt=assembly::validate_native_legacy_row_for_history_test(
                &adapter,input,owner,&row,|index|adapter.export_bit(index)).unwrap();
            assert_eq!(receipt.groups.len(),6);
            assert!(receipt.groups.iter().any(|(name,_)|name==&format!("LegacyMap/{owner}")));
            assert!(receipt.foreign_census<=assembly::MAX_M1_EXTERNAL_CELLS);
            assert_eq!(error(assembly::validate_native_row_for_test(plan,input,&row,|_|panic!("old reader called"))),
                "legacy native consumer binding mismatch");
            if owner==3007 {
                let old_row=old.produce(owner).unwrap();
                for wire in 0..WIDTH {
                    if !active.iter().any(|&(a,b)|a<=wire && wire<b) {
                        assert_eq!(packed_bit(row.packed_bytes(),wire),packed_bit(old_row.packed_bytes(),wire));
                    }
                }
            }
        }
        assert!(adapter.map.active_intervals(3072).unwrap().is_empty());
        assert!(adapter.map.active_intervals(4095).unwrap().is_empty());
        // Component field policy only: at n=a, terminal header may be an anchor.
        let cut=Map::new(1984,11,E).unwrap();
        let active=cut.active_intervals(1983).unwrap();
        assert!(!active.iter().any(|&(a,b)|a<=BASE && BASE<b));
        assert!(active.iter().any(|&(a,b)|a<=SMAX && SMAX<b));
    }

    #[test]
    fn candidate_import_and_helper_faults() {
        let (input,plan)=checked_fixture();
        let adapter=LegacyNativeAdapter::compile(plan,input).unwrap();
        let producer=NativeOwnerProducer::new_for_legacy_history(plan,input,&adapter).unwrap();
        let owner=3007usize;
        let row=producer.produce(owner).unwrap();
        let bits=import_bits_from_packed(&adapter,&producer,owner);
        let candidate=|index|bits.get(&index).copied().map(Ok).unwrap_or_else(||adapter.export_bit(index));
        assert!(adapter.map_failures(owner,&row,candidate).unwrap().is_empty());
        assembly::validate_native_legacy_row_for_history_test(&adapter,input,owner,&row,candidate).unwrap();
        let mut helper=row.clone();
        assembly::flip_native_row_bit_for_test(&mut helper,RATIO+155).unwrap();
        assert_eq!(residual_rows(adapter.map_failures(owner,&helper,candidate).unwrap(),owner),vec![8352,9422]);
        assert!(error(assembly::validate_native_legacy_row_for_history_test(
            &adapter,input,owner,&helper,candidate)).contains("LegacyMap/3007 residual row"));
        let mut padding=row.clone();
        assembly::flip_native_row_bit_for_test(&mut padding,BASE+BANK-1).unwrap();
        assert_eq!(residual_rows(adapter.map_failures(owner,&padding,candidate).unwrap(),owner),vec![BANK-1]);
        let mut own_high=row.clone();
        assembly::flip_native_row_bit_for_test(&mut own_high,D_LOCAL+223).unwrap();
        assert!(residual_rows(adapter.map_failures(owner,&own_high,candidate).unwrap(),owner).contains(&8122));
        let foreign_d:Vec<_>=adapter.map.imports(owner as u64).unwrap().into_iter()
            .filter(|imp|imp.kind==Kind::Difficulty && imp.owner!=owner as u64).collect();
        assert_eq!(foreign_d.iter().map(|x|x.owner).collect::<Vec<_>>(),vec![2046,3006]);
        for (i,imp) in foreign_d.iter().copied().enumerate() {
            let target=adapter.map.input_index(imp,223).unwrap();
            let failures=adapter.map_failures(owner,&row,|index| {
                let bit=candidate(index)?; Ok(if index==target {!bit}else{bit})
            }).unwrap();
            assert_eq!(residual_rows(failures,owner),vec![8350+134*i]);
            let other=foreign_d[1-i];
            assert!((0..224).any(|b|candidate(adapter.map.input_index(imp,b).unwrap()).unwrap()
                !=candidate(adapter.map.input_index(other,b).unwrap()).unwrap()));
            let failures=adapter.map_failures(owner,&row,|index| {
                if index/WIDTH==imp.owner as usize && (D_LOCAL..D_LOCAL+224).contains(&(index%WIDTH)) {
                    candidate(other.owner as usize*WIDTH+index%WIDTH)
                } else {candidate(index)}
            }).unwrap();
            assert_eq!(residual_rows(failures,owner),vec![8350+134*i]);
        }
        let time=adapter.map.imports(owner as u64).unwrap().into_iter()
            .find(|imp|imp.kind==Kind::Timestamp && imp.owner==1023).unwrap();
        let sign=adapter.map.input_index(time,63).unwrap();
        assert_eq!(residual_rows(adapter.map_failures(owner,&row,|index| {
            let bit=candidate(index)?;Ok(if index==sign {!bit}else{bit})
        }).unwrap(),owner),vec![8351,10008]);
        assert_eq!(error(adapter.map_failures(owner,&row,|_|Err("missing candidate import".into()))),
            "missing candidate import");
        let target=adapter.map.input_index(foreign_d[0],223).unwrap();
        assert!(error(assembly::validate_native_legacy_row_for_history_test(
            &adapter,input,owner,&row,|index| {let bit=candidate(index)?;Ok(if index==target {!bit}else{bit})}
        )).contains("LegacyMap/3007 residual row"));
        assert_eq!(error(producer.produce_fault_for_test(owner,AssemblyFault::MissingClaim {
            owner:owner as u64,wire:BASE })),format!("missing claim owner{owner} wire{BASE}"));
    }

    #[test]
    fn binding_cache_and_collector_guards() {
        let input=fixtures::legacy_prefix_for_test();
        let short=NativePrefix::from_raw_iter(3,(1..=3).map(|h|input.raw(h).map(|x|x.to_vec()))).unwrap();
        assert_eq!(error(native_cap_summary(&short)),"legacy native cap requires N3073");
        let original_terminal=crate::work_tree_work::native_decode(input.compact_n_bits(HEADERS).unwrap()).unwrap();
        // Synthetic scalar boundaries only: preserve RAW1..3072 and the terminal
        // parent/genesis linkage. These changed nBits do not claim PoW or DAA validity.
        for (compact,shift) in [(0x09020000u32,65usize),(0x09010000u32,64usize)] {
            let expected=BigUint::one()<<shift;
            assert_eq!(crate::work_tree_work::native_decode(compact).unwrap(),expected);
            let mut terminal=input.header(HEADERS).unwrap();
            terminal.n_bits=compact;
            let terminal_raw=terminal.encode().unwrap();
            let changed=NativePrefix::from_raw_iter(HEADERS,(1..=HEADERS).map(|height| {
                if height==HEADERS {Ok(terminal_raw.clone())} else {input.raw(height).map(|raw|raw.to_vec())}
            })).unwrap();
            if shift==65 {
                assert_eq!(error(native_cap_summary(&changed)),"legacy native e64 cap failed at height3073");
            } else {
                let summary=native_cap_summary(&changed).unwrap();
                assert_eq!(summary.maximum,expected);
                assert_eq!(summary.height,HEADERS);
                assert_eq!(summary.total,BigUint::from_bytes_be(&input.total_be28())-&original_terminal+expected);
            }
        }
        let (input,plan)=checked_fixture();
        assert_eq!(error(LegacyNativeAdapter::compile_e(plan,input,63)),"legacy native diagnostic cap requires e64");
        let adapter=LegacyNativeAdapter::compile(plan,input).unwrap();
        let producer=NativeOwnerProducer::new_for_legacy_history(plan,input,&adapter).unwrap();
        let old=NativeOwnerProducer::new(plan,input).unwrap();
        let row=producer.produce(0).unwrap();
        let duplicate=WorkTreeHistoryPlan::compile(3073,12,input.root(),input.total_be28()).unwrap();
        assert_eq!(error(NativeOwnerProducer::new_for_legacy_history(&duplicate,input,&adapter)),
            "legacy native adapter identity mismatch");
        assert_eq!(error(adapter.check(plan,&short)),"legacy native adapter identity mismatch");
        let mut wrong=row.clone();let mut binding=adapter.binding();binding[0]^=1;
        wrong.set_legacy_binding_for_test(Some(binding));
        assert_eq!(error(assembly::validate_native_legacy_row_for_history_test(
            &adapter,input,0,&wrong,|_|panic!("binding rejection read candidate"))),
            "legacy native consumer binding mismatch");
        assert_eq!(error(assembly::validate_native_legacy_row_for_history_test(
            &adapter,input,1,&row,|_|panic!("owner rejection read candidate"))),"legacy native row owner mismatch");
        let old_row=assembly::metadata_native_row_for_test(&old,0).unwrap();
        assert_eq!(error(assembly::validate_native_legacy_row_for_history_test(
            &adapter,input,0,&old_row,|_|panic!("old row read candidate"))),"legacy native consumer binding mismatch");
        assert_eq!(error(assembly::validate_native_row_for_history_test(
            plan,input,&row,|_|panic!("new row read old candidate"))),"legacy native consumer binding mismatch");
        {
            let old_positive=old.produce(0).unwrap();
            let receipt=assembly::validate_native_row_for_history_test(
                plan,input,&old_positive,|index|adapter.export_bit(index)).unwrap();
            assert_eq!(receipt.groups.len(),5);
        }
        for fault in [assembly::NativeRowFileFault::Root,assembly::NativeRowFileFault::Total,
            assembly::NativeRowFileFault::Class,assembly::NativeRowFileFault::Length] {
            let wrong=assembly::native_row_file_fault_for_test(row.clone(),fault);
            assert_eq!(error(assembly::validate_native_legacy_row_for_history_test(
                &adapter,input,0,&wrong,|_|panic!("metadata rejection read candidate"))),"legacy native row identity mismatch");
        }
        let mut mixed=row.clone();mixed.set_max_binding_for_test(Some([9;32]));
        assert_eq!(error(assembly::validate_native_legacy_row_for_history_test(
            &adapter,input,0,&mixed,|_|panic!("mixed mode read candidate"))),"legacy native MAX mixing");
        let mut permission=plan.physical_assignment_replacement_mask(0).unwrap();permission[BASE+BANK]=true;
        assert_eq!(error(adapter.extend_mask(0,permission)),"legacy native parent mask identity mismatch");
        assert_eq!(error(producer.produce(4096)),"native owner outside original slot domain");
        let (ensure,read)=fixtures::legacy_cache_errors_for_test(&producer,plan).unwrap();
        assert_eq!(ensure,"native row cache has no adapter binding transport");
        assert_eq!(read,ensure);
        let temp=std::env::temp_dir();
        let path=temp.join(format!("nipopow-legacy-native-producer-{}.bits",std::process::id()));
        assert!(!path.exists());let mut calls=0;
        assert_eq!(error(assembly::write_native_window_for_test(&producer,&path,16,|_| {
            calls+=1;Err("callback must not run".into())
        })),"legacy native producer has no old binding transport");
        assert_eq!(calls,0);assert!(!path.exists());
        for bad_owner in [0usize,15] {
            let path=temp.join(format!("nipopow-legacy-native-callback-{}-{bad_owner}.bits",std::process::id()));
            assert!(!path.exists());let mut calls=0;
            let result=assembly::write_native_window_for_test(&old,&path,16,|owner| {
                calls+=1;let mut row=assembly::metadata_native_row_for_test(&old,owner)?;
                if owner==bad_owner {row.set_legacy_binding_for_test(Some(adapter.binding()));}
                Ok(row)
            });
            assert_eq!(error(result),"legacy native consumer binding mismatch");
            assert_eq!(calls,bad_owner+1);assert!(!path.exists());
        }
        // Release the large N3073 producers before the independent old N3 MAX path.
        drop(old);
        drop(producer);
        drop(adapter);
        let max_plan=WorkTreeHistoryPlan::compile(3,2,short.root(),short.total_be28()).unwrap();
        let max=crate::max_header_adapter::MaxHeaderAdapter::compile(&max_plan).unwrap();
        assert_eq!(error(assembly::validate_native_max_row_for_history_test(&max,&short,&row)),
            "legacy native consumer binding mismatch");
        let max_producer=NativeOwnerProducer::new_for_max_history(&max_plan,&short,&max).unwrap();
        let max_row=max_producer.produce(0).unwrap();
        let receipt=assembly::validate_native_max_row_for_history_test(&max,&short,&max_row).unwrap();
        assert_eq!(receipt.groups.len(),6);
    }
}
