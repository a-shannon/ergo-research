//! Fixed Mainnet descriptor and bounded A1 allocation accounting.
use blake2::{digest::{Update,VariableOutput},Blake2bVar};
use num_bigint::BigUint;
use serde::Serialize;
use serde_json::{json,Value};
use crate::daa_finish;
use crate::daa_integer::{self,Epoch,Inputs,WindowInputs,Count};
use crate::daa_regression::{Increment,PredictionInput,Progress};

pub const Q_HEX:&str="FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141";
pub const GENESIS_ID_HEX:&str="b0244dfc267baca974a4caee06120321562784303a8a688976ae56170e4d175b";
pub const GENESIS_TIMESTAMP_MS:i64=1_561_978_977_137;
pub const GENESIS_FIXTURE_SHA256:&str="b1fedd8377288558956a7551efe01973ba221880bf009290fbace963ccec1aab";
pub const NATIVE_ADJUSTMENT_SHA256:&str="a38ae5fa599e2e61971823c335a0261369a2c4aaa030b11f82454cefdc73b170";
pub const NATIVE_SERIALIZER_SHA256:&str="5a5f688af0dd5bc4a5398e0de609b3aea0bf3ca6b7048738e86485243f1f30b7";
pub const CONTRACT_SHA256:&str="1d8d75a8c1980999036e4903e3ba79f225c6f7e106df284327dd858deb7c1633";
pub const SCOPE_SHA256:&str="197c50d002a5c277215abbb80c13f43b4e337e486aff1cb873f41d885dc224c7";

#[derive(Clone,Serialize)]
pub struct MainnetDescriptor{
    pub profile:&'static str,pub network:&'static str,pub genesis_id_hex:&'static str,
    pub genesis_timestamp_ms:i64,pub genesis_fixture_sha256:&'static str,
    pub desired_interval_ms:u64,pub legacy_epoch:u64,pub eip_epoch:u64,pub use_last_epochs:u64,
    pub eip_activation_child:u64,pub reset_children:[u64;2],
    pub genesis_difficulty_hex:&'static str,pub activation_difficulty_hex:&'static str,
    pub autolykos_q_hex:&'static str,pub q_semantics:&'static str,
    pub compact_semantics:&'static str,pub timestamp_semantics:&'static str,
    pub quotient_semantics:&'static str,pub coordinate_layout:&'static str,
    pub limb_bits:usize,pub compact_max_positive_exponent:u64,
    pub legacy_offsets:[u64;9],pub eip_offsets:[u64;9],
    pub native_adjustment_sha256:&'static str,pub native_serializer_sha256:&'static str,
    pub compiled_slice:&'static str,
}
pub fn descriptor()->MainnetDescriptor{
    MainnetDescriptor{profile:"daa-decode-quotient-a1-v1",network:"Ergo-Mainnet",
        genesis_id_hex:GENESIS_ID_HEX,genesis_timestamp_ms:GENESIS_TIMESTAMP_MS,
        genesis_fixture_sha256:GENESIS_FIXTURE_SHA256,
        desired_interval_ms:120_000,legacy_epoch:1024,eip_epoch:128,use_last_epochs:8,
        eip_activation_child:844_673,reset_children:[417_792,417_793],
        genesis_difficulty_hex:"011765000000",activation_difficulty_hex:"6f98d5000000",
        autolykos_q_hex:Q_HEX,q_semantics:"secp256k1 group order, positive decoded difficulty <= Q",
        compact_semantics:"numeric aliases accepted, exponent up to 34; sign bit must be zero",
        timestamp_semantics:"signed 64-bit Scala subtraction wraps modulo 2^64; MIN included",
        quotient_semantics:"positive numerator; signed quotient truncates toward zero; remainder nonnegative and < abs(denominator)",
        coordinate_layout:"LSB-first Boolean bits, 16-bit columns, fixed sparse residual topology",
        limb_bits:16,compact_max_positive_exponent:34,
        legacy_offsets:[0,1024,2048,3072,4096,5120,6144,7168,8192],
        eip_offsets:[0,128,256,384,512,640,768,896,1024],
        native_adjustment_sha256:NATIVE_ADJUSTMENT_SHA256,native_serializer_sha256:NATIVE_SERIALIZER_SHA256,
        compiled_slice:"numeric nBits decode + signed Long delta + d*120000*E / delta for E=1024,128"}
}
pub fn q()->BigUint{BigUint::parse_bytes(Q_HEX.as_bytes(),16).expect("fixed literal")}
pub fn descriptor_bytes()->Vec<u8>{serde_json::to_vec(&descriptor()).expect("fixed descriptor")}
pub fn descriptor_blake2b256()->[u8;32]{
    let mut h=Blake2bVar::new(32).expect("digest length");h.update(&descriptor_bytes());
    let mut out=[0;32];h.finalize_variable(&mut out).expect("digest length");out
}
fn compiled_source_digest(bytes:&[u8])->String{
    let mut h=Blake2bVar::new(32).expect("digest length");h.update(bytes);
    let mut out=[0;32];h.finalize_variable(&mut out).expect("digest length");hex(&out)
}
pub fn source_pins()->Value{
    json!({"daa_witness_scope_sha256":SCOPE_SHA256,
        "compiled_daa_integer_blake2b256":compiled_source_digest(include_bytes!("daa_integer.rs")),
        "compiled_daa_count_blake2b256":compiled_source_digest(include_bytes!("daa_count.rs")),
        "compiled_daa_regression_blake2b256":compiled_source_digest(include_bytes!("daa_regression.rs")),
        "compiled_daa_finish_blake2b256":compiled_source_digest(include_bytes!("daa_finish.rs")),
        "native_adjustment_sha256":NATIVE_ADJUSTMENT_SHA256,
        "native_serializer_sha256":NATIVE_SERIALIZER_SHA256,
        "genesis_fixture_sha256":GENESIS_FIXTURE_SHA256,
        "genesis_profile_sha256":"4492aa3b84aa92e73bf3919d1e87f47d20c5d23bac560962e1951c2e8361310a",
        "autolykos_q_source":"secp256k1 group order, k256 0.13.4 ORDER_HEX",
        "mining_scala_sha256":"897a55afa7d78a30861d6d148206dde6f8385c7b46de94f018bc89b9953f030c",
        "crypto_constants_scala_sha256":"c15430744dfbb685d4e136565111f34b5a2fdd3df78bae955ebbc346eda23b34",
        "bc_dlog_group_scala_sha256":"4cbab01eb2c70757798913bba43ebe2f748802af6cfaa42813b9d4178bf76bc7",
        "platform_scala_sha256":"74a1822e7c3d7e87143e022aab22bd881915da4699e22da1f1f5b661efaaf353",
        "crypto_context_jvm_scala_sha256":"1f3c6e2ecfb9b9385db5db096f844519517785beed3b14c341799581960a2fd1",
        "autolykos_q_source_sha256":"39703b0cfe286f69e06561e4f2e12cc60dd916b87279ee66e25235f9f69ccbd9"})
}

/// The first bound is a single fresh quotient. It says nothing about the
/// remaining DAA regression, clamps, normalization or historical imports.
pub fn one(epoch:Epoch)->Result<daa_integer::Compiled,String>{
    daa_integer::compile(epoch,&q(),Inputs{nbits:0x03000001,start_timestamp:0,end_timestamp:1},false)
}
pub fn eight(epoch:Epoch)->Result<daa_integer::CompiledWindow,String>{
    daa_integer::compile_eight(epoch,&q(),mature_input(epoch)?.window,false)
}
/// Synthetic shape fixture for one mature nine-header sample window. The eight
/// quotient endpoints start at the second sample height; authenticated headers,
/// schedule selectors, and history imports are deliberately outside this join.
fn mature_input(epoch:Epoch)->Result<PredictionInput,String>{
    let step=i64::try_from(epoch.multiplier()).map_err(|_|"DAA epoch step exceeds i64")?;
    let mut timestamps=[GENESIS_TIMESTAMP_MS;9];
    for i in 1..timestamps.len(){
        timestamps[i]=timestamps[i-1].checked_add(step).ok_or("synthetic DAA timestamp overflow")?;
    }
    let parent_height=match epoch{Epoch::Legacy=>427_008u64,Epoch::Eip=>844_672u64};
    let first_quotient_endpoint=parent_height.checked_sub(7*epoch.length())
        .ok_or("mature sample height underflow")?;
    let x0=u32::try_from(first_quotient_endpoint).map_err(|_|"DAA endpoint exceeds u32")?;
    Ok(PredictionInput{window:WindowInputs{nbits:[0x03000001;8],timestamps},x0})
}
fn compile_mature(epoch:Epoch)->Result<daa_finish::CompiledFinish,String>{
    daa_finish::compile_finish(epoch,&q(),mature_input(epoch)?,false)
}
fn mature_a1_progress(epoch:Epoch)->Result<Progress,String>{
    let input=mature_input(epoch)?;
    let (_,progress)=daa_integer::compile_eight_extended(epoch,&q(),input.window,false,
        |builder,_|Ok(Progress::from(builder.progress())))?;
    Ok(progress)
}
fn progress_json(value:Progress)->Value{
    json!({"live_bits":value.live_bits,"rows":value.rows,"terms":value.terms})
}
fn increment_json(value:Increment)->Value{
    json!({"before":progress_json(value.before),"after":progress_json(value.after),
        "added_live_bits":value.added_live_bits,"added_rows":value.added_rows,
        "added_terms":value.added_terms})
}
fn mature_summary(epoch:Epoch,compiled:&daa_finish::CompiledFinish)->Result<Value,String>{
    let a2=compiled.joined.joined.increment;
    let a3=compiled.joined.increment;
    let a4=compiled.increment;
    let a1=a2.before;
    let count=&compiled.joined.joined.joined.count;
    if mature_a1_progress(epoch)?!=a1{
        return Err("embedded A1 progress differs from the same-input standalone pre-padding count".into());
    }
    if compiled.joined.joined.joined.circuit.is_some(){
        return Err("count-only DAA composition unexpectedly materialized sparse terms".into());
    }
    if a3.before!=a2.after || a4.before!=a3.after
        || count.live_bits!=a4.after.live_bits
        || a4.after.rows.checked_add(count.padding_bits)!=Some(count.residual_rows)
        || a4.after.terms.checked_add(count.padding_bits)!=Some(count.terms)
        || count.padded_input_bits!=count.live_bits.next_power_of_two()
        || count.padded_rows!=count.residual_rows.next_power_of_two(){
        return Err("A1-A4 DAA count ledger or final padding mismatch".into());
    }
    let input=mature_input(epoch)?;
    Ok(json!({
        "epoch":format!("{epoch:?}"),
        "fixture":{"kind":"synthetic mature Mainnet-shaped arithmetic window",
            "sample_headers":9,"quotients":8,"compact_nbits_hex":"03000001",
            "decoded_difficulty":"1","timestamp_anchor_ms":GENESIS_TIMESTAMP_MS,
            "timestamp_step_ms":epoch.multiplier(),"first_quotient_endpoint_height":input.x0,
            "boundary_parent_height":input.x0 as u64+7*epoch.length(),
            "authentic_history":false},
        "compile_mode":{"sparse_circuit_materialized":false,
            "witness_assignment_materialized":true},
        "phases":{"A1":progress_json(a1),"A2_regression":increment_json(a2),
            "A3_prediction":increment_json(a3),"A4_finish_and_clamps":increment_json(a4)},
        "aggregate":summary(count),
        "local_domains":{"input_log2":count.padded_input_bits.trailing_zeros(),
            "row_log2":count.padded_rows.trailing_zeros(),
            "fits_each_local_domain_below_2pow20":count.padded_input_bits<=1<<20
                && count.padded_rows<=1<<20,
            "candidate_placement_in_current_free_ranges":placement(count),
            "global_embedding_and_shared_layout":"not measured"}
    }))
}
fn hex(bytes:&[u8])->String{bytes.iter().map(|b|format!("{b:02x}")).collect()}
fn summary(c:&Count)->Value{
    json!({"live_bits":c.live_bits,"input_bits":c.input_bits,"padded_input_bits":c.padded_input_bits,
        "residual_rows":c.residual_rows,"padded_rows":c.padded_rows,"terms":c.terms,
        "boolean_rows":c.boolean_rows,"linear_rows":c.linear_rows,"bilinear_rows":c.bilinear_rows,
        "maximum_degree":c.maximum_degree,"maximum_column_signed_abs_bits":c.maximum_column_signed_abs_bits,
        "source_nbits_bits":c.source_nbits_bits,"source_timestamp_bits":c.source_timestamp_bits,
        "decoded_bits":c.decoded_bits,"wrapped_delta_bits":c.wrapped_delta_bits,
        "denominator_bits":c.denominator_bits,"numerator_bits":c.numerator_bits,
        "quotient_bits":c.quotient_bits,"remainder_bits":c.remainder_bits,
        "quotient_sign_bits":c.quotient_sign_bits,"remainder_sign_bits":c.remainder_sign_bits,
        "auxiliary_bits":c.auxiliary_bits,
        "padding_bits":c.padding_bits,"retained_witness_capacity_fields":c.witness_capacity,
        "retained_term_capacity":c.retained_terms_capacity,"peak_row_terms":c.peak_row_terms,
        "peak_row_capacity_terms":c.peak_row_capacity_terms,
        "topology_blake2b256":hex(&c.topology_blake2b256),
        "sparse_admission":{"dimension_at_most_24":c.padded_input_bits.trailing_zeros()<=24
                && c.padded_rows.trailing_zeros()<=24,
            "input_dimension_at_most_24":c.padded_input_bits.trailing_zeros()<=24,
            "row_dimension_at_most_24":c.padded_rows.trailing_zeros()<=24,
            "base_terms_at_most_2pow20":c.terms<=(1<<20),"log_copies":0,
            "copy_domain_growth":"unqualified for global embedding"}})
}
fn aligned(start:usize,alignment:usize)->usize{start.div_ceil(alignment)*alignment}
fn placement(c:&Count)->Value{
    let gaps=[(655628usize,720896usize),(796160,851968),(991232,1048576)];
    let candidates=gaps.iter().map(|&(start,end)|{
        let begin=aligned(start,16);let upper=begin.checked_add(c.padded_input_bits).unwrap_or(usize::MAX);
        json!({"start":start,"end_exclusive":end,"aligned_start":begin,
            "alignment_waste":begin-start,"compiled_bank_bits":c.padded_input_bits,
            "compiled_live_bits":c.live_bits,"candidate_end_exclusive":upper,
            "fits_compiled_slice":upper<=end,"opening_projection":"pending global embedding"})
    }).collect::<Vec<_>>();
    json!({"alignment_bits":16,"candidate_intervals":candidates,
        "fits_any_contiguous_interval_for_compiled_slice":gaps.iter().any(|&(s,e)|aligned(s,16)+c.padded_input_bits<=e)})
}
pub fn report()->Result<Value,String>{
    let legacy=one(Epoch::Legacy)?;let eip=one(Epoch::Eip)?;
    let eight_legacy=eight(Epoch::Legacy)?;let eight_eip=eight(Epoch::Eip)?;
    let mature_legacy=compile_mature(Epoch::Legacy)?;
    let mature_eip=compile_mature(Epoch::Eip)?;
    Ok(json!({"profile":"daa-decode-quotient-a1-v1","contract_sha256":CONTRACT_SHA256,
        "descriptor":descriptor(),"descriptor_blake2b256":hex(&descriptor_blake2b256()),
        "source_pins":source_pins(),
        "one_legacy":summary(&legacy.count),"one_eip":summary(&eip.count),
        "eight_legacy":summary(&eight_legacy.count),"eight_eip":summary(&eight_eip.count),
        "count_extension":"daa-a4-mature-window-count-v1",
        "composed_mature_arithmetic":{"scope":"A1-A4 arithmetic over one synthetic mature nine-header window; no historical imports or branch selectors",
            "legacy":mature_summary(Epoch::Legacy,&mature_legacy)?,
            "eip":mature_summary(Epoch::Eip,&mature_eip)?,
            "exclusions":["sample-to-committed-slot authentication","branch and activation selectors",
                "early one/two-sample legacy branches","inactive-slot and epoch-bank projections",
                "work-tree U224 composition","global GKR/PCS embedding"]},
        "placement":{"shared_free_intervals_after_b1_endpoint_reservation":[[655628,720896],[796160,851968],[991232,1048576]],
            "shared_total_free_bits":178420,"per_header_one_legacy":placement(&legacy.count),
            "per_header_one_eip":placement(&eip.count),
            "per_header_eight_legacy":placement(&eight_legacy.count),
            "per_header_eight_eip":placement(&eight_eip.count),
            "compact_epoch_banks":"uncompiled: imports, masks, aliases, inactive slots, projection and global embedding pending"},
        "pending_consumers":["regression and signed Int32 forecast","both EIP clamps",
            "compact re-encoding and normalization","branch precedence and reset/inherit selectors",
            "authenticated historical imports and their 18 fixed grid families",
            "genesis timestamp equality to serializer bits and reachable-Mainnet lemma",
            "complete DAA/work U224 alias and global GKR/PCS embedding"],
        "decision":"A1-A4 mature arithmetic compiles in one local composition; complete Mainnet DAA allocation remains unresolved because early branches, selectors, authenticated imports, projections and global embedding are not counted"}))
}

#[cfg(test)]
mod tests{
    use super::*;
    use ark_bn254::Fr;
    use ark_ff::{One,Zero};
    use std::collections::BTreeMap;
    use crate::{daa_finish::FinishOutput,
        daa_integer::{ExternalBits,OutputBits,SubtractTrace},
        daa_regression::{PredictionOutput,RegressionOutput,SignedAlias},
        gkr::Gate,sparse::{Circuit,Term},work_tree_layout::{self,Bank}};

    fn packed_hash_core_copy(slot:usize,core:usize)->usize{
        assert!(core<crate::header_hash::CORE_COPIES);
        slot*(work_tree_layout::WIDTH/crate::header_hash::CORE_WIDTH)+core
    }
    fn read_packed_hash_slot(source:&crate::packed::PackedFile,slot:usize,slot_count:usize)
        ->Result<Vec<Fr>,String>{
        if slot>=slot_count{return Err("header hash source slot outside packed input".into());}
        let copies_per_slot=work_tree_layout::WIDTH/crate::header_hash::CORE_WIDTH;
        let mut values=Vec::with_capacity(work_tree_layout::WIDTH);
        for copy in 0..copies_per_slot{
            values.extend(source.read_copy(crate::header_hash::CORE_WIDTH,
                slot*copies_per_slot+copy)?);
        }
        Ok(values)
    }
    fn tensor_copy_factor(r:&[Fr],u:&[Fr],v:&[Fr],copies:&[usize])->Result<Fr,String>{
        if r.len()!=u.len()||r.len()!=v.len(){return Err("tensor copy point dimensions".into());}
        let domain=1usize.checked_shl(r.len() as u32).ok_or("tensor copy domain overflow")?;
        if copies.iter().any(|copy|*copy>=domain){return Err("tensor copy outside domain".into());}
        Ok(copies.iter().fold(Fr::zero(),|sum,copy|sum
            +crate::work_tree_wiring::eq_index(r,*copy)
                *crate::work_tree_wiring::eq_index(u,*copy)
                *crate::work_tree_wiring::eq_index(v,*copy)))
    }
    fn tensor_sparse_wiring(circuit:&Circuit,shape:&crate::sparse::Shape,
        r_low:&[Fr],u_low:&[Fr],v_low:&[Fr],r_copy:&[Fr],u_copy:&[Fr],v_copy:&[Fr],
        copies:&[usize])->Result<[Fr;4],String>{
        if r_low.len()!=shape.row_bits||u_low.len()!=shape.input_bits||v_low.len()!=shape.input_bits{
            return Err("tensor sparse base point dimensions".into());
        }
        let local=crate::sparse::wiring(circuit,shape,r_low,u_low,v_low)
            .map_err(|error|error.to_string())?;
        let factor=tensor_copy_factor(r_copy,u_copy,v_copy,copies)?;
        Ok(std::array::from_fn(|index|local[index]*factor))
    }
    fn brute_eq_weight(point:&[Fr],index:usize)->Fr{
        let mut weight=Fr::from(1u64);
        for (bit,value) in point.iter().enumerate(){
            weight*=if (index>>bit)&1==1{*value}else{Fr::from(1u64)-*value};
        }
        weight
    }
    fn explicit_tensor_coefficients(circuit:&Circuit,row_bits:usize,input_bits:usize,
        copies:&[usize],r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{
        let mut out=[Fr::zero();4];
        for copy in copies{for term in &circuit.terms{
            let gate=&term.gate;
            let weight=brute_eq_weight(r,(*copy<<row_bits)|term.row)
                *brute_eq_weight(u,(*copy<<input_bits)|gate.left)
                *brute_eq_weight(v,(*copy<<input_bits)|gate.right);
            for (value,coefficient) in out.iter_mut().zip([gate.c0,gate.c1,gate.c2,gate.c3]){
                *value+=weight*coefficient;
            }
        }}
        out
    }
    fn decode_boolean_index(bits:&[Fr])->usize{
        bits.iter().enumerate().fold(0usize,|index,(bit,value)|{
            assert!(*value==Fr::zero()||*value==Fr::from(1u64));
            index|(((!value.is_zero()) as usize)<<bit)
        })
    }
    fn explicit_boolean_tensor_coefficients(circuit:&Circuit,row_bits:usize,input_bits:usize,
        copies:&[usize],r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{
        let row=decode_boolean_index(r);let left=decode_boolean_index(u);let right=decode_boolean_index(v);
        let mut out=[Fr::zero();4];
        for copy in copies{for term in &circuit.terms{
            let gate=&term.gate;
            if row==((*copy<<row_bits)|term.row)&&left==((*copy<<input_bits)|gate.left)
                &&right==((*copy<<input_bits)|gate.right){
                for (value,coefficient) in out.iter_mut().zip([gate.c0,gate.c1,gate.c2,gate.c3]){
                    *value+=coefficient;
                }
            }
        }}
        out
    }
    fn bool_point(bits:usize,index:usize)->Vec<Fr>{
        (0..bits).map(|bit|Fr::from(((index>>bit)&1) as u64)).collect()
    }

    #[test]
    fn tensor_hash_wiring_matches_explicit_active_copy_expansion(){
        let term=|row,left,right,coefficients:[u64;4]|Term{row,gate:Gate{left,right,
            c0:Fr::from(coefficients[0]),c1:Fr::from(coefficients[1]),
            c2:Fr::from(coefficients[2]),c3:Fr::from(coefficients[3])}};
        let circuit=Circuit{input_len:8,row_count:4,terms:vec![
            term(0,1,4,[2,3,5,7]),term(0,1,4,[11,13,17,19]),
            term(2,6,3,[23,29,31,37]),term(3,0,7,[41,43,47,53]) ]};
        let shape=crate::sparse::validate(&circuit,0).unwrap();
        let core_copies=(0..80).collect::<Vec<_>>();
        let active_slots=(0..10).collect::<Vec<_>>();

        // Boolean points independently select every copy boundary, including
        // the 7→8 header transition, final active item, and inactive padding.
        for &(copy,bits,active) in &[(0,7,80),(7,7,80),(8,7,80),(71,7,80),
            (72,7,80),(79,7,80),(80,7,80),(127,7,80),
            (0,4,10),(8,4,10),(9,4,10),(10,4,10),(15,4,10)]{
            let active_ids=if bits==7{&core_copies}else{&active_slots};
            assert_eq!(active_ids.len(),active);
            let selected=&circuit.terms[0];let g=&selected.gate;
            let r=bool_point(shape.row_bits+bits,(copy<<shape.row_bits)|selected.row);
            let u=bool_point(shape.input_bits+bits,(copy<<shape.input_bits)|g.left);
            let v=bool_point(shape.input_bits+bits,(copy<<shape.input_bits)|g.right);
            let expected=explicit_boolean_tensor_coefficients(&circuit,shape.row_bits,
                shape.input_bits,active_ids,&r,&u,&v);
            let actual=tensor_sparse_wiring(&circuit,&shape,&r[..shape.row_bits],
                &u[..shape.input_bits],&v[..shape.input_bits],&r[shape.row_bits..],
                &u[shape.input_bits..],&v[shape.input_bits..],active_ids).unwrap();
            assert_eq!(actual,expected,"boolean tensor point at copy {copy}");
            assert_eq!(expected[0],if active_ids.contains(&copy){Fr::from(13u64)}else{Fr::zero()},
                "fixture must expose selected and omitted copies at {copy}");
        }

        // All 128 compression-copy diagonals catch a missing active copy; all
        // sixteen boundary slots check the active 0..9 roster and padding 10..15.
        for copy in 0..128{
            let r=bool_point(7,copy);let u=bool_point(7,copy);let v=bool_point(7,copy);
            assert_eq!(tensor_copy_factor(&r,&u,&v,&core_copies).unwrap(),
                Fr::from((copy<80) as u64),"core active-copy diagonal {copy}");
        }
        for slot in 0..16{
            let r=bool_point(4,slot);let u=bool_point(4,slot);let v=bool_point(4,slot);
            assert_eq!(tensor_copy_factor(&r,&u,&v,&active_slots).unwrap(),
                Fr::from((slot<10) as u64),"boundary active-slot diagonal {slot}");
        }
        let r=bool_point(7,79);let u=bool_point(7,80);let v=bool_point(7,79);
        assert_eq!(tensor_copy_factor(&r,&u,&v,&core_copies).unwrap(),Fr::zero(),
            "different row/input copy indices must not alias");
        let without_last=core_copies.iter().copied().filter(|copy|*copy!=79).collect::<Vec<_>>();
        let selected=&circuit.terms[0];let g=&selected.gate;
        let r=bool_point(shape.row_bits+7,(79<<shape.row_bits)|selected.row);
        let u=bool_point(shape.input_bits+7,(79<<shape.input_bits)|g.left);
        let v=bool_point(shape.input_bits+7,(79<<shape.input_bits)|g.right);
        let omitted=tensor_sparse_wiring(&circuit,&shape,&r[..shape.row_bits],&u[..shape.input_bits],
            &v[..shape.input_bits],&r[shape.row_bits..],&u[shape.input_bits..],
            &v[shape.input_bits..],&without_last).unwrap();
        assert_ne!(omitted,explicit_boolean_tensor_coefficients(&circuit,shape.row_bits,
            shape.input_bits,&core_copies,&r,&u,&v),"omitting compression 79 must be detected");

        // Non-Boolean points compare the factorized callback with a separate
        // direct expansion over every active copy and every explicit term.
        let r=(0..shape.row_bits+7).map(|i|Fr::from(((i*7+3)%13+1) as u64)).collect::<Vec<_>>();
        let u=(0..shape.input_bits+7).map(|i|Fr::from(((i*5+2)%11+1) as u64)).collect::<Vec<_>>();
        let v=(0..shape.input_bits+7).map(|i|Fr::from(((i*3+4)%17+1) as u64)).collect::<Vec<_>>();
        let expected=explicit_tensor_coefficients(&circuit,shape.row_bits,shape.input_bits,
            &core_copies,&r,&u,&v);
        let actual=tensor_sparse_wiring(&circuit,&shape,&r[..shape.row_bits],&u[..shape.input_bits],
            &v[..shape.input_bits],&r[shape.row_bits..],&u[shape.input_bits..],
            &v[shape.input_bits..],&core_copies).unwrap();
        assert_eq!(actual,expected,"non-Boolean tensor expansion");

        for slot in 0..10{for core in 0..crate::header_hash::CORE_COPIES{
            let packed_copy=packed_hash_core_copy(slot,core);
            assert_eq!(packed_copy,slot*16+core);
            for wire in [0,1,crate::header_hash::CORE_WIDTH-1]{
                assert_eq!(packed_copy*crate::header_hash::CORE_WIDTH+wire,
                    slot*work_tree_layout::WIDTH+core*crate::header_hash::CORE_WIDTH+wire,
                    "packed core coordinate slot={slot}, core={core}, wire={wire}");
            }
        }}
    }

    const PHASE_BANKS:[(&str,usize,usize);4]=[
        ("daa_a1",819_200,32_768),
        ("daa_a2",663_552,8_192),
        ("daa_a3",688_128,32_768),
        ("daa_a4",991_232,8_192),
    ];
    const DAA_BANK_SLACK_ROWS:usize=16_384;

    /// Replayable fixture producer for the mature DAA plus header projection.
    /// It deliberately borrows the compiled sources instead of retaining a
    /// second, combined `EdgeTerm` roster for GKR.
    struct MatureDaaProofEdgeSource<'a>{
        original:&'a Circuit,
        wire_map:&'a [usize],
        used:[usize;4],
        result_slot:usize,
        daa_row_start:usize,
        bank_slack_rows:usize,
        aliases:&'a [Term],
        child_aliases:&'a [Term],
        x0_aliases:&'a [Term],
        projection:&'a Circuit,
        projection_residual_rows:usize,
        projection_row_start:usize,
        projection_aux_start:usize,
        projection_aux_end:usize,
        projection_aux_bank_start:usize,
        serializer_offset:usize,
        serializer_input_len:usize,
        projection_slots:usize,
    }

    impl MatureDaaProofEdgeSource<'_>{
        fn emit_edge(&self,source_slot:usize,family_row:usize,term:Term,
            sink:&mut dyn FnMut(crate::sparse_stream_roster::EdgeTerm)->Result<(),String>)
            ->Result<(),String>{
            let width=work_tree_layout::WIDTH;
            let input_len=width.checked_mul(16).ok_or("DAA proof input width overflow")?;
            if source_slot>=16||family_row>=1<<17||term.row!=family_row
                ||term.gate.left>=input_len||term.gate.right>=input_len{
                return Err("mature DAA edge exceeds slot, row, or input allocation".into());
            }
            sink(crate::sparse_stream_roster::EdgeTerm{source_slot,family_row,term})
        }

        fn projection_wire(&self,slot:usize,wire:usize)->Result<usize,String>{
            let width=work_tree_layout::WIDTH;
            if slot>=self.projection_slots||wire>=self.serializer_input_len{
                return Err("projection source slot or wire outside allocation".into());
            }
            let local=if wire>=self.projection_aux_start{
                if wire>=self.projection_aux_end{
                    return Err("projection references unallocated auxiliary padding".into());
                }
                self.projection_aux_bank_start.checked_add(wire-self.projection_aux_start)
                    .ok_or("projection auxiliary coordinate overflow")?
            }else{
                self.serializer_offset.checked_add(wire)
                    .ok_or("projection serializer coordinate overflow")?
            };
            if local>=width{return Err("projection wire exceeds packed slot".into());}
            slot.checked_mul(width).and_then(|base|base.checked_add(local))
                .ok_or_else(||"projection global coordinate overflow".into())
        }

        fn emit_all(&self,
            sink:&mut dyn FnMut(crate::sparse_stream_roster::EdgeTerm)->Result<(),String>)
            ->Result<(),String>{
            self.emit_matching(None,sink)
        }

        fn emit_matching(&self,endpoint_filter:Option<(bool,usize)>,
            sink:&mut dyn FnMut(crate::sparse_stream_roster::EdgeTerm)->Result<(),String>)
            ->Result<(),String>{
            let width=work_tree_layout::WIDTH;
            let expected_slack=PHASE_BANKS.iter().map(|(_,_,bank_width)|*bank_width).sum::<usize>()
                .checked_sub(self.used.iter().sum::<usize>());
            if self.wire_map.len()!=self.original.input_len||self.result_slot>=16
                ||self.projection_slots>16||expected_slack.is_none_or(|slack|slack!=self.bank_slack_rows)
                ||self.used.iter().enumerate().any(|(index,live)|*live>PHASE_BANKS[index].2)
                ||self.projection_aux_start>=self.projection_aux_end
                ||self.projection_aux_end>self.serializer_input_len
                ||self.projection_row_start.checked_add(self.projection_residual_rows)
                    .is_none_or(|end|end>1<<17)
                ||self.projection.terms.iter().any(|term|term.row>=self.projection_residual_rows){
                return Err("mature DAA edge source layout changed".into());
            }
            let daa_base=self.result_slot.checked_mul(width)
                .ok_or("DAA result-slot coordinate overflow")?;
            if endpoint_filter.is_none_or(|(_,slot)|slot==self.result_slot){
                for original in &self.original.terms{
                    let gate=&original.gate;
                    let left_active=!gate.c1.is_zero()||!gate.c3.is_zero();
                    let right_active=!gate.c2.is_zero()||!gate.c3.is_zero();
                    let mapped_left=if left_active{
                        daa_base.checked_add(*self.wire_map.get(gate.left)
                            .ok_or("DAA left wire outside compiled map")?)
                            .ok_or("DAA left coordinate overflow")?
                    }else if right_active{
                        daa_base.checked_add(*self.wire_map.get(gate.right)
                            .ok_or("DAA right wire outside compiled map")?)
                            .ok_or("DAA right coordinate overflow")?
                    }else{
                        daa_base.checked_add(PHASE_BANKS[0].1)
                            .ok_or("DAA zero-row coordinate overflow")?
                    };
                    let mapped_right=if right_active{
                        daa_base.checked_add(*self.wire_map.get(gate.right)
                            .ok_or("DAA right wire outside compiled map")?)
                            .ok_or("DAA right coordinate overflow")?
                    }else{mapped_left};
                    let mapped=Term{row:original.row,gate:Gate{left:mapped_left,right:mapped_right,
                        c0:gate.c0,c1:gate.c1,c2:gate.c2,c3:gate.c3}};
                    self.emit_edge(self.result_slot,mapped.row,mapped,sink)?;
                }

                let mut slack_index=0usize;
                for ((_,bank_start,bank_width),live) in PHASE_BANKS.into_iter().zip(self.used){
                    for wire in bank_start+live..bank_start+bank_width{
                        let row=self.daa_row_start.checked_add(slack_index)
                            .ok_or("DAA bank-slack row overflow")?;
                        let endpoint=daa_base.checked_add(wire)
                            .ok_or("DAA bank-slack coordinate overflow")?;
                        self.emit_edge(self.result_slot,row,Term{row,gate:Gate{left:endpoint,
                            right:endpoint,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}},sink)?;
                        slack_index+=1;
                    }
                }
                if slack_index!=self.bank_slack_rows{
                    return Err("DAA bank-slack count changed".into());
                }
            }
            for alias in self.aliases.iter().chain(self.child_aliases).chain(self.x0_aliases){
                if endpoint_filter.is_some_and(|(left,slot)|{
                    let endpoint=if left{alias.gate.left}else{alias.gate.right};
                    endpoint/width!=slot
                }){continue;}
                self.emit_edge(self.result_slot,alias.row,alias.clone(),sink)?;
            }

            for slot in 0..self.projection_slots{
                if endpoint_filter.is_some_and(|(_,endpoint_slot)|endpoint_slot!=slot){continue;}
                for original in &self.projection.terms{
                    let row=self.projection_row_start.checked_add(original.row)
                        .ok_or("projection row overflow")?;
                    let gate=&original.gate;
                    let mapped=Term{row,gate:Gate{
                        left:self.projection_wire(slot,gate.left)?,
                        right:self.projection_wire(slot,gate.right)?,
                        c0:gate.c0,c1:gate.c1,c2:gate.c2,c3:gate.c3}};
                    self.emit_edge(slot,row,mapped,sink)?;
                }
            }
            Ok(())
        }

        fn emit_endpoint(&self,left_endpoint:bool,slot:usize,
            sink:&mut dyn FnMut(crate::sparse_stream_roster::EdgeTerm)->Result<(),String>)
            ->Result<(),String>{
            if slot>=16{return Err("mature DAA endpoint slot outside input".into());}
            self.emit_matching(Some((left_endpoint,slot)),sink)
        }
    }

    fn child_nbits_alias_terms(child_nbits:&[usize;32],wire_map:&[usize],daa_witness:&[Fr],
        serializer:&crate::serializer::Compiled,serializer_assignment:&[Fr],serializer_offset:usize,
        result_slot:usize,row_start:usize,global_input_len:usize,a4_end:usize,daa_live_end:usize,
        coordinate_values:&mut BTreeMap<usize,Fr>)->Vec<Term>{
        assert_eq!(daa_witness.len(),wire_map.len());
        assert_eq!(serializer_assignment.len(),serializer.circuit.input_len);
        assert_eq!(serializer.layout.fields.n_bits.len(),32);
        let (a4_start,a4_width)=(PHASE_BANKS[3].1,PHASE_BANKS[3].2);
        let slot_offset=result_slot*work_tree_layout::WIDTH;
        let mut aliases=Vec::with_capacity(32);
        for (bit,&daa_wire) in child_nbits.iter().enumerate(){
            assert!(daa_wire>=a4_end&&daa_wire<daa_live_end,
                "child nBits wire is outside the post-A4 child-join extension");
            assert!(daa_wire<wire_map.len()&&daa_wire<daa_witness.len());
            let daa_local=wire_map[daa_wire];
            let serializer_wire=serializer.layout.fields.n_bits[bit];
            let serializer_local=serializer_offset+serializer_wire;
            assert!(daa_local>=a4_start&&daa_local<a4_start+a4_width,
                "child nBits output is outside the A4 candidate bank");
            assert!(serializer_wire<serializer_assignment.len()
                &&serializer_local<crate::header_hash::AUX_OFFSET);
            let left=slot_offset+daa_local;
            let right=slot_offset+serializer_local;
            assert!(left<global_input_len&&right<global_input_len&&left!=right);
            let left_value=daa_witness[daa_wire];
            let right_value=serializer_assignment[serializer_wire];
            assert_eq!(left_value,right_value,
                "computed child nBits differs from canonical serializer field");
            assert!(coordinate_values.insert(left,left_value).is_none(),
                "duplicate DAA child coordinate");
            assert!(coordinate_values.insert(right,right_value).is_none(),
                "duplicate child serializer coordinate");
            let row=row_start+aliases.len();
            aliases.push(Term{row,gate:Gate{left,right,c0:Fr::zero(),c1:Fr::one(),
                c2:-Fr::one(),c3:Fr::zero()}});
        }
        aliases
    }

    fn streamed_boundary_residuals(joined:&crate::segment_relation::Joined,slot:usize,
        released:&[std::ops::Range<usize>],local_input:&[Fr])->(Vec<Fr>,usize){
        let width=work_tree_layout::WIDTH;assert_eq!(width,crate::segment_relation::HEADER_WIDTH);
        assert_eq!(local_input.len(),width);
        let slot_offset=slot*width;let mut rows=vec![Fr::zero();joined.boundary.row_count];
        let skipped=crate::segment_relation::emit_boundary_edges_for_slot(joined,slot,released,
            &mut |edge|{
                if edge.source_slot!=slot||edge.family_row>>20!=1
                    ||edge.term.gate.left/width!=slot||edge.term.gate.right/width!=slot{
                    return Err("streamed child boundary edge escaped its slot or family".into());
                }
                let mut gate=edge.term.gate.clone();gate.left-=slot_offset;gate.right-=slot_offset;
                rows[edge.term.row]+=gate.evaluate(local_input);Ok(())
            }).unwrap();
        (rows,skipped)
    }

    fn slot_alias_residuals(aliases:&[Term],slot:usize,local_input:&[Fr])->Vec<Fr>{
        let width=work_tree_layout::WIDTH;let slot_offset=slot*width;
        aliases.iter().map(|term|{
            assert_eq!(term.gate.left/width,slot);assert_eq!(term.gate.right/width,slot);
            let mut gate=term.gate.clone();gate.left-=slot_offset;gate.right-=slot_offset;
            gate.evaluate(local_input)
        }).collect()
    }

    struct RemovePackedFixture(std::path::PathBuf);
    impl Drop for RemovePackedFixture{
        fn drop(&mut self){let _=std::fs::remove_file(&self.0);}
    }

    fn check_wire(wire:usize,map:&[usize]){
        assert!(wire<map.len(),"exported wire outside original witness: {wire}");
        assert!(map[wire]<work_tree_layout::WIDTH,"mapped wire outside global input");
    }
    fn check_wires(wires:&[usize],map:&[usize]){
        for &wire in wires{check_wire(wire,map);}
    }
    fn check_matrix(wires:&[Vec<usize>],map:&[usize]){
        for row in wires{check_wires(row,map);}
    }
    fn check_rows(rows:&[usize],row_count:usize){
        assert!(rows.iter().all(|&row|row<row_count),"exported row outside residual domain");
    }
    fn check_external(bits:&ExternalBits,map:&[usize]){
        check_wires(&bits.nbits,map);check_wires(&bits.start_timestamp,map);
        check_wires(&bits.end_timestamp,map);
    }
    fn check_output_bits(bits:&OutputBits,map:&[usize]){
        check_wires(&bits.decoded_difficulty,map);check_wires(&bits.wrapped_delta,map);
        check_wires(&bits.denominator_magnitude,map);check_wires(&bits.numerator,map);
        check_wires(&bits.quotient_magnitude,map);check_wire(bits.quotient_negative,map);
        check_wires(&bits.remainder_magnitude,map);check_wire(bits.remainder_negative,map);
    }
    fn check_subtract_trace(trace:&SubtractTrace,map:&[usize]){
        check_wire(trace.initial_borrow,map);check_wires(&trace.differences,map);
        check_wires(&trace.borrows,map);check_wires(&trace.minuend_wires,map);
        check_wires(&trace.subtrahend_wires,map);
    }
    fn check_signed_alias(alias:&SignedAlias,map:&[usize],row_count:usize){
        check_wires(&alias.magnitude,map);check_wire(alias.negative,map);
        check_rows(&alias.magnitude_binding_rows,row_count);
        assert!(alias.sign_binding_row<row_count);
    }
    fn check_regression(output:&RegressionOutput,map:&[usize],row_count:usize){
        for alias in &output.aliases{check_signed_alias(alias,map,row_count);}
        check_wires(&output.positive_sum,map);check_wires(&output.negative_sum,map);
        check_wires(&output.sum_magnitude,map);check_wire(output.sum_negative,map);
        check_wires(&output.numerator,map);check_wires(&output.slope_magnitude,map);
        check_wire(output.slope_negative,map);check_wires(&output.remainder,map);
        check_wire(output.remainder_negative,map);check_matrix(&output.division_carries,map);
        check_wire(output.remainder_range_final_borrow,map);
    }
    fn check_prediction(output:&PredictionOutput,map:&[usize],row_count:usize){
        check_wires(&output.x0_bits,map);check_matrix(&output.grid_x,map);
        check_signed_alias(&output.b_alias,map,row_count);check_wires(&output.sum_x,map);
        check_wires(&output.y_magnitude,map);check_wire(output.y_negative,map);
        check_wires(&output.py_magnitude,map);check_wires(&output.b_sum_x_magnitude,map);
        check_wires(&output.x_magnitude,map);check_wire(output.x_negative,map);
        check_wires(&output.a_magnitude,map);check_wire(output.a_negative,map);
        check_wires(&output.a_remainder,map);check_wire(output.a_remainder_negative,map);
        check_matrix(&output.a_division_carries,map);check_wire(output.a_range_final_borrow,map);
        check_wires(&output.point_twos,map);check_wires(&output.point_magnitude,map);
        check_wire(output.point_negative,map);check_rows(&output.point_binding_rows,row_count);
        check_wires(&output.b_point_magnitude,map);check_wires(&output.term_magnitude,map);
        check_wire(output.term_negative,map);check_wires(&output.term_remainder,map);
        check_wire(output.term_remainder_negative,map);check_matrix(&output.term_division_carries,map);
        check_wire(output.term_range_final_borrow,map);check_wires(&output.prediction_magnitude,map);
        check_wire(output.prediction_negative,map);
    }
    fn check_finish(output:&FinishOutput,map:&[usize]){
        check_wire(output.use_prediction,map);check_wires(&output.predictive,map);
        if let Some(wires)=&output.lower{check_wires(wires,map);}
        if let Some(wires)=&output.upper{check_wires(wires,map);}
        if let Some(wires)=&output.limited{check_wires(wires,map);}
        if let Some(wires)=&output.average_magnitude{check_wires(wires,map);}
        if let Some(wire)=output.average_negative{check_wire(wire,map);}
        if let Some(wires)=&output.precompact{check_wires(wires,map);}
        check_wires(&output.numeric_result,map);
    }
    fn check_exported_handles(compiled:&daa_finish::CompiledFinish,map:&[usize],row_count:usize){
        let a1=&compiled.joined.joined.joined;
        for external in &a1.external{check_external(external,map);}
        for output in &a1.output{check_output_bits(output,map);}
        for trace in &a1.subtract_traces{check_subtract_trace(trace,map);}
        check_wires(&a1.carry_wires,map);
        check_regression(&compiled.joined.joined.output,map,row_count);
        check_prediction(&compiled.joined.output,map,row_count);
        check_finish(&compiled.output,map);
    }
    fn circuit_residuals(circuit:&Circuit,witness:&[Fr])->Vec<Fr>{
        assert_eq!(witness.len(),circuit.input_len);
        let mut rows=vec![Fr::zero();circuit.row_count];
        for term in &circuit.terms{
            assert!(term.row<circuit.row_count);
            assert!(term.gate.left<circuit.input_len && term.gate.right<circuit.input_len);
            rows[term.row]+=term.gate.evaluate(witness);
        }
        rows
    }
    fn scalar_eq_weight(point:&[Fr],index:usize)->Fr{
        point.iter().enumerate().fold(Fr::one(),|weight,(bit,challenge)|{
            weight*if (index>>bit)&1==1{*challenge}else{Fr::one()-challenge}
        })
    }

    #[test]
    fn mature_a1_to_a4_count_is_one_padded_composition_without_sparse_materialization(){
        for epoch in [Epoch::Legacy,Epoch::Eip]{
            let compiled=compile_mature(epoch).unwrap();
            let a1=mature_a1_progress(epoch).unwrap();
            let a2=compiled.joined.joined.increment;
            let a3=compiled.joined.increment;
            let a4=compiled.increment;
            let count=&compiled.joined.joined.joined.count;
            assert_eq!(a1,a2.before);
            assert_eq!(a2.before.live_bits+a2.added_live_bits,a2.after.live_bits);
            assert_eq!(a2.before.rows+a2.added_rows,a2.after.rows);
            assert_eq!(a2.before.terms+a2.added_terms,a2.after.terms);
            assert_eq!(a3.before,a2.after);
            assert_eq!(a4.before,a3.after);
            assert_eq!(count.live_bits,a4.after.live_bits);
            assert_eq!(a4.after.rows.checked_add(count.padding_bits),Some(count.residual_rows));
            assert_eq!(a4.after.terms.checked_add(count.padding_bits),Some(count.terms));
            assert_eq!(count.padded_input_bits,count.live_bits.next_power_of_two());
            assert_eq!(count.padded_rows,count.residual_rows.next_power_of_two());
            assert!(compiled.joined.joined.joined.circuit.is_none());
            println!("{}",serde_json::to_string_pretty(&mature_summary(epoch,&compiled).unwrap()).unwrap());
        }
    }

    #[test]
    fn mature_a1_to_a4_reindex_preserves_residuals_in_candidate_phase_banks(){
        let baseline=work_tree_layout::shared_baseline().unwrap();
        for epoch in [Epoch::Legacy,Epoch::Eip]{
            let compiled=daa_finish::compile_finish(epoch,&q(),mature_input(epoch).unwrap(),true).unwrap();
            let a2=&compiled.joined.joined.increment;
            let a3=&compiled.joined.increment;
            let a4=&compiled.increment;
            let count=&compiled.joined.joined.joined.count;
            let original=compiled.joined.joined.joined.circuit.as_ref().unwrap();
            let old_witness=&compiled.joined.joined.joined.witness;
            assert_eq!(a3.before,a2.after);assert_eq!(a4.before,a3.after);
            assert_eq!(count.live_bits,a4.after.live_bits);
            assert_eq!(old_witness.len(),count.padded_input_bits);
            assert_eq!(original.input_len,count.padded_input_bits);
            assert_eq!(original.row_count,count.padded_rows);
            assert_eq!(original.terms.len(),count.terms);
            assert_eq!(count.padded_input_bits,65_536);

            let a1_end=a2.before.live_bits;
            let a2_end=a2.after.live_bits;
            let a3_end=a3.after.live_bits;
            let padded=count.padded_input_bits;
            let spans=[(0,a1_end),(a1_end,a2_end),(a2_end,a3_end),(a3_end,padded)];
            let used=spans.map(|(start,end)|end-start);
            let mut banks=baseline.inventory.banks.clone();
            for ((role,start,width),live) in PHASE_BANKS.into_iter().zip(used){
                let end=start+width;
                assert!(live<=width,"{role} phase exceeds reserved bank");
                assert!(baseline.inventory.free_ranges.iter().any(|(lo,hi)|start>=*lo && end<=*hi),
                    "{role} candidate is not contained in a baseline free interval");
                banks.push(Bank{role:role.into(),start,end,live_bits:live,
                    alignment:width,padding_bits:width-live,last_coordinate:end-1,
                    opening:"test-only aligned DAA phase bank".into()});
            }
            work_tree_layout::validate_banks(&banks).unwrap();
            assert_eq!(used[3],a4.after.live_bits-a3_end+count.padding_bits);
            assert_eq!(used.iter().sum::<usize>(),padded);

            let mut wire_map=vec![usize::MAX;padded];
            let mut occupied=vec![false;work_tree_layout::WIDTH];
            for (phase,((old_start,old_end),(_,bank_start,width)))
                in spans.into_iter().zip(PHASE_BANKS.into_iter()).enumerate(){
                assert_eq!(bank_start%width,0);
                for old in old_start..old_end{
                    let mapped=bank_start+(old-old_start);
                    assert!(mapped<bank_start+width);
                    assert!(!occupied[mapped],"phase bank coordinate collision at {mapped}");
                    occupied[mapped]=true;wire_map[old]=mapped;
                }
                assert!(used[phase]<=width);
            }
            assert!(wire_map.iter().all(|&wire|wire!=usize::MAX));
            assert_eq!(occupied.iter().filter(|&&value|value).count(),padded);
            check_exported_handles(&compiled,&wire_map,original.row_count);

            let mut mapped_witness=vec![Fr::zero();work_tree_layout::WIDTH];
            for (old,&mapped) in wire_map.iter().enumerate(){mapped_witness[mapped]=old_witness[old];}
            let mut mapped_terms=Vec::with_capacity(original.terms.len()+16_384);
            for term in &original.terms{
                let mut gate=term.gate.clone();
                gate.left=wire_map[gate.left];gate.right=wire_map[gate.right];
                mapped_terms.push(Term{row:term.row,gate});
            }
            let mut next_row=count.residual_rows;
            for ((_,start,width),live) in PHASE_BANKS.into_iter().zip(used){
                for wire in start+live..start+width{
                    assert!(!occupied[wire]);occupied[wire]=true;
                    mapped_terms.push(Term{row:next_row,gate:Gate{left:wire,right:0,
                        c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}});
                    next_row+=1;
                }
            }
            let added_padding_rows=next_row-count.residual_rows;
            assert_eq!(added_padding_rows,81_920-padded);
            assert!(next_row<=count.padded_rows,"candidate slack constraints exceed row domain");
            assert!(mapped_terms.len()<=daa_integer::MAX_MATERIAL_TERMS);
            assert_eq!(occupied.iter().filter(|&&value|value).count(),81_920);
            let mapped=Circuit{input_len:work_tree_layout::WIDTH,row_count:original.row_count,terms:mapped_terms};
            assert!(mapped.terms.windows(2).all(|pair|pair[0].row<=pair[1].row));

            let expected=circuit_residuals(original,old_witness);
            assert!(expected.iter().all(Zero::is_zero),"synthetic DAA witness has nonzero residuals");
            assert_eq!(circuit_residuals(&mapped,&mapped_witness),expected);

            let cases=[(0,Fr::from(2u64)),(a1_end,Fr::from(2u64)),
                (a2_end,Fr::from(2u64)),(a3_end,Fr::from(2u64)),
                (count.live_bits,Fr::one())];
            for (old_wire,value) in cases{
                assert!(old_wire<padded);
                let mut changed=old_witness.clone();changed[old_wire]=value;
                let mut changed_mapped=vec![Fr::zero();work_tree_layout::WIDTH];
                for (old,&new) in wire_map.iter().enumerate(){changed_mapped[new]=changed[old];}
                let before=circuit_residuals(original,&changed);
                let after=circuit_residuals(&mapped,&changed_mapped);
                assert!(before.iter().any(|residual|!residual.is_zero()),"isolated mutant was not detected");
                assert_eq!(after,before,"residual changed after remapping wire {old_wire}");
            }
            let mut cross_phase_rows:BTreeMap<usize,u8>=BTreeMap::new();
            for term in &original.terms{
                let mut phase_mask=0u8;
                for (wire,used_coefficient) in [
                    (term.gate.left,!term.gate.c1.is_zero()||!term.gate.c3.is_zero()),
                    (term.gate.right,!term.gate.c2.is_zero()||!term.gate.c3.is_zero())]{
                    if used_coefficient{
                        let phase=spans.iter().position(|(start,end)|wire>=*start&&wire<*end).unwrap();
                        phase_mask|=1<<phase;
                    }
                }
                *cross_phase_rows.entry(term.row).or_default()|=phase_mask;
            }
            assert!(cross_phase_rows.values().any(|mask|mask.count_ones()>1),
                "fixture does not exercise cross-phase rows");
            println!("{epoch:?}: live={}, input={}, rows={}, terms={}, candidate-slack={}, mapped-terms={}",
                count.live_bits,padded,count.residual_rows,count.terms,added_padding_rows,mapped.terms.len());
        }
    }

    #[test]
    fn synthetic_child_nbits_alias_joins_slot9_streamed_private_boundary(){
        use num_bigint::{BigInt,Sign};
        const DAA_RESULT_SLOT:usize=9;
        assert_eq!(work_tree_layout::WIDTH,crate::segment_relation::HEADER_WIDTH);
        let epoch=Epoch::Eip;let x0=129u32;
        let interval=120_000u64*epoch.length();
        let timestamps=std::array::from_fn(|index|index as i64*interval as i64);
        let window=WindowInputs{nbits:[0x0300_0001;8],timestamps};
        let values:[BigInt;8]=std::array::from_fn(|sample|{
            let difficulty=crate::work_tree_work::native_decode(window.nbits[sample]).unwrap();
            BigInt::from_biguint(Sign::Plus,difficulty)*BigInt::from(interval)
                /BigInt::from(window.timestamps[sample+1]-window.timestamps[sample])
        });
        let prediction=crate::daa_regression::native_prediction_oracle(x0 as i64,epoch,&values).2;
        let last=crate::work_tree_work::native_decode(window.nbits[7]).unwrap();
        let child_numeric=daa_finish::native_finish_oracle(epoch,&prediction,&values[7],&last).unwrap();
        let (child_nbits,decoded_child)=daa_finish::native_positive_compact_roundtrip(&child_numeric);
        assert_eq!(decoded_child,child_numeric);
        assert_eq!(child_nbits,0x0101_0000,"fixture must expose exponent-one compact aliases");
        let compiled=daa_finish::compile_finish_with_child(epoch,&q(),
            PredictionInput{window,x0},child_nbits,true).unwrap();
        let original=compiled.joined.joined.joined.circuit.as_ref().unwrap();
        let daa_witness=&compiled.joined.joined.joined.witness;
        assert!(circuit_residuals(original,daa_witness).iter().all(Zero::is_zero),
            "the compiled synthetic A1-A4 child witness must satisfy its owner relation");

        let count=&compiled.joined.joined.joined.count;
        let a2=&compiled.joined.joined.increment;let a3=&compiled.joined.increment;
        let a4=&compiled.increment;assert_eq!(a3.before,a2.after);assert_eq!(a4.before,a3.after);
        let a1_end=a2.before.live_bits;let a2_end=a2.after.live_bits;
        let a3_end=a3.after.live_bits;let a4_end=a4.after.live_bits;
        let spans=[(0,a1_end),(a1_end,a2_end),(a2_end,a3_end),(a3_end,count.padded_input_bits)];
        let mut wire_map=vec![usize::MAX;count.padded_input_bits];
        for ((old_start,old_end),(_,bank_start,width)) in spans.into_iter().zip(PHASE_BANKS){
            assert!(old_end-old_start<=width,"compiled DAA phase exceeds its candidate bank");
            for old in old_start..old_end{
                let mapped=bank_start+(old-old_start);assert!(mapped<work_tree_layout::WIDTH);
                assert_eq!(wire_map[old],usize::MAX,"compiled DAA candidate banks overlap");
                wire_map[old]=mapped;
            }
        }
        assert!(wire_map.iter().all(|&wire|wire!=usize::MAX));
        let child_wire_indices=compiled.child_nbits.as_ref().expect("compiled child nBits wires");
        assert_eq!(child_wire_indices.len(),32);
        let daa_serializer=crate::serializer::build(None).unwrap();
        let child_fields=crate::serializer::Fields{version:4,parent_id:[0x11;32],
            ad_proofs_root:[0x22;32],transactions_root:[0x33;32],state_root:[0x44;33],
            timestamp:timestamps[8],extension_root:[0x55;32],n_bits:child_nbits,
            height:x0+8*epoch.length() as u32,votes:[1,2,3],pk:[0;33],w:[0;33],
            nonce:[0x80;8],payload_len:0,payload:[0;255]};
        let serialized=daa_serializer.assign(&child_fields);
        let mut boundary=crate::segment_relation::build(Some(&child_fields)).unwrap();
        crate::segment_relation::attach_serializer_relation(&mut boundary).unwrap();
        assert_eq!(boundary.serializer.layout.fields.n_bits,daa_serializer.layout.fields.n_bits);
        let released=crate::segment_relation::padding_anchor_row_ranges_for_wires(&boundary,
            &[PHASE_BANKS[3].1..PHASE_BANKS[3].1+PHASE_BANKS[3].2]).unwrap();
        assert_eq!(released,vec![348_440..356_632]);

        let mut local_input=boundary.input.take().expect("private child header witness");
        assert_eq!(local_input.len(),work_tree_layout::WIDTH);
        assert_eq!(&local_input[crate::header_hash::SERIALIZER_OFFSET..crate::header_hash::AUX_OFFSET],
            serialized.as_slice());
        for (old,&mapped) in wire_map.iter().enumerate(){
            assert!(local_input[mapped].is_zero(),
                "DAA candidate wire {mapped} overlaps a populated child-header wire");
            local_input[mapped]=daa_witness[old];
        }
        let mut coordinate_values=BTreeMap::new();
        let alias_row_start=count.residual_rows+DAA_BANK_SLACK_ROWS;
        assert!(alias_row_start+32<=count.padded_rows,
            "synthetic child aliases must fit after reserved DAA bank-slack rows");
        let aliases=child_nbits_alias_terms(child_wire_indices,&wire_map,daa_witness,
            &daa_serializer,&serialized,crate::header_hash::SERIALIZER_OFFSET,DAA_RESULT_SLOT,
            alias_row_start,16*work_tree_layout::WIDTH,a4_end,count.live_bits,&mut coordinate_values);
        assert_eq!(aliases.len(),32);
        for (bit,alias) in aliases.iter().enumerate(){
            assert_eq!(alias.row,alias_row_start+bit);
            assert!((PHASE_BANKS[3].1..PHASE_BANKS[3].1+PHASE_BANKS[3].2)
                .contains(&(alias.gate.left%work_tree_layout::WIDTH)),
                "true child alias must consume a released A4 wire");
            assert_eq!(alias.gate.left%work_tree_layout::WIDTH,wire_map[child_wire_indices[bit]]);
            assert_eq!(alias.gate.right%work_tree_layout::WIDTH,
                crate::header_hash::SERIALIZER_OFFSET+daa_serializer.layout.fields.n_bits[bit]);
        }
        assert!(slot_alias_residuals(&aliases,DAA_RESULT_SLOT,&local_input)
            .iter().all(Zero::is_zero),"compiled synthetic child aliases must hold on the shared slot witness");

        let (unreleased_rows,unreleased_count)=streamed_boundary_residuals(&boundary,
            DAA_RESULT_SLOT,&[],&local_input);
        assert_eq!(unreleased_count,0);
        let unreleased_failures=unreleased_rows.iter().enumerate()
            .filter_map(|(row,value)|(!value.is_zero()).then_some(row)).collect::<Vec<_>>();
        assert!(!unreleased_failures.is_empty(),"nonzero synthetic A4 outputs must expose the anchor conflict");
        assert!(unreleased_failures.iter().all(|row|released[0].contains(row)),
            "only the mapped A4 anchor bank may conflict with the synthetic child output");
        let (released_rows,released_count)=streamed_boundary_residuals(&boundary,
            DAA_RESULT_SLOT,&released,&local_input);
        assert_eq!(released_count,8_192);
        assert!(released_rows.iter().all(Zero::is_zero),
            "the synthetic DAA child and private boundary must join after releasing only A4 anchors");

        let owner_mutation_bit=17;
        assert_eq!(crate::work_tree_work::native_decode(child_nbits^1).unwrap(),decoded_child,
            "low mantissa bit must preserve the decoded child target in this fixture");
        assert_ne!(crate::work_tree_work::native_decode(child_nbits^(1u32<<owner_mutation_bit)).unwrap(),
            decoded_child,"owner mutant must change the decoded child target");
        let alias=&aliases[owner_mutation_bit];
        let daa_local=alias.gate.left%work_tree_layout::WIDTH;
        let mut daa_mutant=daa_witness.to_vec();
        daa_mutant[child_wire_indices[owner_mutation_bit]]=
            Fr::one()-daa_mutant[child_wire_indices[owner_mutation_bit]];
        assert!(circuit_residuals(original,&daa_mutant).iter().any(|value|!value.is_zero()),
            "the DAA owner circuit must reject a child-output mutation that changes decoded difficulty");
        let mut local_mutant=local_input.clone();
        local_mutant[daa_local]=Fr::one()-local_mutant[daa_local];
        let (mutant_boundary_rows,mutant_released_count)=streamed_boundary_residuals(&boundary,
            DAA_RESULT_SLOT,&released,&local_mutant);
        assert_eq!(mutant_released_count,8_192);
        assert!(mutant_boundary_rows.iter().all(Zero::is_zero),
            "the boundary alone admits a mutation to its released A4 wire");
        assert_eq!(slot_alias_residuals(&aliases,DAA_RESULT_SLOT,&local_mutant)
            .iter().enumerate().filter_map(|(row,value)|(!value.is_zero()).then_some(row)
            ).collect::<Vec<_>>(),vec![owner_mutation_bit],
            "the synthetic child alias must reject precisely the released owner-mutant wire");
        let mut serializer_mutant=local_input.clone();
        let serializer_local=alias.gate.right%work_tree_layout::WIDTH;
        serializer_mutant[serializer_local]=Fr::one()-serializer_mutant[serializer_local];
        assert_eq!(slot_alias_residuals(&aliases,DAA_RESULT_SLOT,&serializer_mutant)
            .iter().enumerate().filter_map(|(row,value)|(!value.is_zero()).then_some(row)
            ).collect::<Vec<_>>(),vec![owner_mutation_bit],
            "the same synthetic alias must reject an isolated serializer-side mutation");

        let raw_alias_bit=0;
        let mut equivalent_daa_mutant=daa_witness.to_vec();
        equivalent_daa_mutant[child_wire_indices[raw_alias_bit]]=
            Fr::one()-equivalent_daa_mutant[child_wire_indices[raw_alias_bit]];
        assert!(circuit_residuals(original,&equivalent_daa_mutant).iter().all(Zero::is_zero),
            "the DAA owner relation binds decoded difficulty, so an equivalent compact encoding remains valid");
        let raw_alias=&aliases[raw_alias_bit];
        let raw_alias_local=raw_alias.gate.left%work_tree_layout::WIDTH;
        let mut equivalent_local_mutant=local_input.clone();
        equivalent_local_mutant[raw_alias_local]=Fr::one()-equivalent_local_mutant[raw_alias_local];
        let (equivalent_boundary_rows,equivalent_released_count)=streamed_boundary_residuals(&boundary,
            DAA_RESULT_SLOT,&released,&equivalent_local_mutant);
        assert_eq!(equivalent_released_count,8_192);
        assert!(equivalent_boundary_rows.iter().all(Zero::is_zero),
            "the released boundary alone admits a same-target compact encoding");
        assert_eq!(slot_alias_residuals(&aliases,DAA_RESULT_SLOT,&equivalent_local_mutant)
            .iter().enumerate().filter_map(|(row,value)|(!value.is_zero()).then_some(row)
            ).collect::<Vec<_>>(),vec![raw_alias_bit],
            "the exact raw-header alias must reject a same-target compact encoding that differs from the header");

        // Select actual DAA, private-boundary, and BLAKE-core terms through
        // the global edge encoding without materializing their full roster.
        // Address checks and the GKR path both use production coordinates;
        // only six selected edges are streamed into the global relation.
        const INPUT_BITS:usize=24;
        const SLOT_BITS:usize=4;
        const BASE_ROW_BITS:usize=20;
        const FAMILY_BITS:usize=2;
        const INPUT_WIDTH:usize=1<<(INPUT_BITS-SLOT_BITS);
        const MEMBER_ROW_BITS:[usize;3]=[17,19,20];
        use crate::sparse_stream_roster::EdgeTerm;
        use ark_serialize::CanonicalSerialize;
        assert_eq!(INPUT_WIDTH,work_tree_layout::WIDTH,
            "the packed global domain must use one header width per slot");
        assert_eq!(INPUT_WIDTH*(1<<SLOT_BITS),1<<INPUT_BITS,
            "the slot stride and count must reconstruct the flattened input domain");

        let owner=original.terms.iter().find(|term|!term.gate.c3.is_zero())
            .expect("compiled DAA relation has a bilinear owner term");
        let owner_edge=EdgeTerm{source_slot:DAA_RESULT_SLOT,family_row:owner.row,
            term:Term{row:owner.row,gate:Gate{left:DAA_RESULT_SLOT*INPUT_WIDTH+wire_map[owner.gate.left],
                right:DAA_RESULT_SLOT*INPUT_WIDTH+wire_map[owner.gate.right],
                c0:owner.gate.c0,c1:owner.gate.c1,c2:owner.gate.c2,c3:owner.gate.c3}}};
        let x0_wire=compiled.joined.output.x0_bits[0];
        let mut source_fields=child_fields.clone();source_fields.height=x0;
        let source_assignment=daa_serializer.assign(&source_fields);
        let x0_height_wire=daa_serializer.layout.fields.height[0];
        let x0_alias_row=alias_row_start+aliases.len();
        assert!(x0_alias_row<count.padded_rows&&x0_wire<a4_end,
            "sampled x0-to-height alias must remain within the actual DAA row and A3 wire banks");
        assert_eq!(daa_witness[x0_wire],source_assignment[x0_height_wire],
            "the DAA x0 witness must equal slot 1's serialized height");
        let x0_alias_edge=EdgeTerm{source_slot:DAA_RESULT_SLOT,family_row:x0_alias_row,
            term:Term{row:x0_alias_row,gate:Gate{
                left:DAA_RESULT_SLOT*INPUT_WIDTH+wire_map[x0_wire],
                right:INPUT_WIDTH+crate::header_hash::SERIALIZER_OFFSET+x0_height_wire,
                c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}}};

        let mut boundary_samples=Vec::<EdgeTerm>::with_capacity(2);
        let ordinary_skipped=crate::segment_relation::emit_boundary_edges_for_slot(
            &boundary,1,&[],&mut |edge|{
                if boundary_samples.is_empty(){boundary_samples.push(edge);}
                Ok(())
            }).unwrap();
        assert_eq!(ordinary_skipped,0);
        let child_boundary_row=boundary.boundary.terms.iter()
            .find(|term|term.row>=released[0].end).expect("child boundary has rows after A4 release").row;
        let child_skipped=crate::segment_relation::emit_boundary_edges_for_slot(
            &boundary,DAA_RESULT_SLOT,&released,&mut |edge|{
                if edge.term.row==child_boundary_row&&boundary_samples.len()==1{
                    boundary_samples.push(edge);
                }
                Ok(())
            }).unwrap();
        assert_eq!(child_skipped,8_192,"child source must release exactly its mapped A4 anchors");
        assert_eq!(boundary_samples.len(),2,"ordinary and child private-boundary samples must emit");
        assert_eq!(boundary_samples[0].source_slot,1);
        assert_eq!(boundary_samples[0].family_row>>BASE_ROW_BITS,1);
        assert_eq!(boundary_samples[1].source_slot,DAA_RESULT_SLOT);
        assert_eq!(boundary_samples[1].family_row>>BASE_ROW_BITS,1);

        let core=boundary.core4.terms.iter().find(|term|term.row<1<<17&&!term.gate.c3.is_zero())
            .expect("private BLAKE core has a bilinear compression term");
        assert_eq!(crate::header_hash::CORE_COPIES,8);
        let mut core_samples=Vec::<EdgeTerm>::with_capacity(2);
        for (slot,copy) in [(1usize,0usize),(DAA_RESULT_SLOT,7usize)]{
            let local_row=(copy<<17)|core.row;
            let local_offset=copy*crate::header_hash::CORE_WIDTH;
            core_samples.push(EdgeTerm{source_slot:slot,
                family_row:(2<<BASE_ROW_BITS)|local_row,
                term:Term{row:local_row,gate:Gate{
                    left:slot*INPUT_WIDTH+local_offset+core.gate.left,
                    right:slot*INPUT_WIDTH+local_offset+core.gate.right,
                    c0:core.gate.c0,c1:core.gate.c1,c2:core.gate.c2,c3:core.gate.c3}}});
        }

        let mut sampled=vec![owner_edge,x0_alias_edge];
        sampled.extend(boundary_samples);
        sampled.extend(core_samples);
        assert_eq!(sampled.len(),6);
        for edge in &sampled{
            let family=edge.family_row>>BASE_ROW_BITS;
            let local=edge.family_row&((1<<BASE_ROW_BITS)-1);
            assert!(family<MEMBER_ROW_BITS.len()&&local<1<<MEMBER_ROW_BITS[family]);
            assert!(edge.source_slot<1<<SLOT_BITS
                &&edge.term.gate.left<INPUT_WIDTH*(1<<SLOT_BITS)
                &&edge.term.gate.right<INPUT_WIDTH*(1<<SLOT_BITS));
            assert!(crate::sparse_stream_roster::global_edge_row(edge.source_slot,
                edge.family_row,SLOT_BITS,BASE_ROW_BITS,FAMILY_BITS,&MEMBER_ROW_BITS).is_ok());
        }

        fn callback_coefficients(edges:&[EdgeTerm],r:&[Fr],u:&[Fr],v:&[Fr])
            ->Result<[Fr;4],String>{
            let mut out=[Fr::zero();4];
            for edge in edges{
                let row=crate::sparse_stream_roster::global_edge_row(edge.source_slot,
                    edge.family_row,SLOT_BITS,BASE_ROW_BITS,FAMILY_BITS,&MEMBER_ROW_BITS)?;
                let gate=&edge.term.gate;
                let weight=crate::work_tree_wiring::eq_index(r,row)
                    *crate::work_tree_wiring::eq_index(u,gate.left)
                    *crate::work_tree_wiring::eq_index(v,gate.right);
                for (sum,coefficient) in out.iter_mut().zip([gate.c0,gate.c1,gate.c2,gate.c3]){
                    *sum+=weight*coefficient;
                }
            }
            Ok(out)
        }
        fn explicit_coefficients(edges:&[EdgeTerm],r:&[Fr],u:&[Fr],v:&[Fr])
            ->Result<[Fr;4],String>{
            let mut out=[Fr::zero();4];
            for edge in edges{
                let family=edge.family_row>>BASE_ROW_BITS;
                let local=edge.family_row&((1<<BASE_ROW_BITS)-1);
                let row=(family<<(BASE_ROW_BITS+SLOT_BITS))
                    |(edge.source_slot<<MEMBER_ROW_BITS[family])|local;
                let gate=&edge.term.gate;
                let weight=brute_eq_weight(r,row)*brute_eq_weight(u,gate.left)
                    *brute_eq_weight(v,gate.right);
                for (sum,coefficient) in out.iter_mut().zip([gate.c0,gate.c1,gate.c2,gate.c3]){
                    *sum+=weight*coefficient;
                }
            }
            Ok(out)
        }
        let x0_index=1usize;
        let target=&sampled[x0_index];
        let boolean_bits=|width:usize,index:usize| (0..width)
            .map(|bit|Fr::from(((index>>bit)&1) as u64)).collect::<Vec<_>>();
        let target_row=crate::sparse_stream_roster::global_edge_row(target.source_slot,
            target.family_row,SLOT_BITS,BASE_ROW_BITS,FAMILY_BITS,&MEMBER_ROW_BITS).unwrap();
        let (boolean_r,boolean_u,boolean_v)=(boolean_bits(26,target_row),
            boolean_bits(INPUT_BITS,target.term.gate.left),boolean_bits(INPUT_BITS,target.term.gate.right));
        let boolean_result=callback_coefficients(&sampled,&boolean_r,&boolean_u,&boolean_v).unwrap();
        assert_eq!(boolean_result,[Fr::zero(),Fr::one(),-Fr::one(),Fr::zero()],
            "Boolean point must isolate the actual cross-slot DAA x0/height alias");
        assert_eq!(boolean_result,explicit_coefficients(&sampled,&boolean_r,&boolean_u,&boolean_v).unwrap());

        let r=(0..26).map(|bit|Fr::from(3+bit as u64*2)).collect::<Vec<_>>();
        let u=(0..INPUT_BITS).map(|bit|Fr::from(5+bit as u64*3)).collect::<Vec<_>>();
        let v=(0..INPUT_BITS).map(|bit|Fr::from(7+bit as u64*5)).collect::<Vec<_>>();
        let nonboolean=callback_coefficients(&sampled,&r,&u,&v).unwrap();
        assert_eq!(nonboolean,explicit_coefficients(&sampled,&r,&u,&v).unwrap(),
            "three-family callback coefficients must match independent bit-loop expansion");

        let omitted=sampled.iter().enumerate().filter_map(|(index,edge)|
            (index!=x0_index).then_some(edge.clone())).collect::<Vec<_>>();
        assert_eq!(callback_coefficients(&omitted,&boolean_r,&boolean_u,&boolean_v).unwrap(),
            [Fr::zero();4],"omitting the selected DAA alias must remove its Boolean evaluation");
        let mut wrong_tag=sampled.clone();
        wrong_tag[0].family_row=(1<<BASE_ROW_BITS)|(wrong_tag[0].family_row&((1<<BASE_ROW_BITS)-1));
        assert_ne!(callback_coefficients(&wrong_tag,&r,&u,&v).unwrap(),nonboolean,
            "wrong family tag must change the sampled callback result");
        let mut wrong_slot=sampled.clone();wrong_slot[x0_index].source_slot-=1;
        assert_ne!(callback_coefficients(&wrong_slot,&r,&u,&v).unwrap(),nonboolean,
            "wrong DAA source slot must change the sampled callback result");

        // Exercise GKR at the production input geometry. Only six selected
        // edges are streamed; their 20-bit local wire labels remain unchanged.
        let mut source_local_input=local_input.clone();
        source_local_input[crate::header_hash::SERIALIZER_OFFSET..
            crate::header_hash::SERIALIZER_OFFSET+source_assignment.len()]
            .copy_from_slice(&source_assignment);
        let visit_full=|left_endpoint:bool,slot:usize,
            sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>|{
            for edge in &sampled{
                let global_wire=if left_endpoint{edge.term.gate.left}else{edge.term.gate.right};
                if global_wire/INPUT_WIDTH==slot{sink(edge.clone())?;}
            }
            Ok(())
        };
        let load_full=|slot:usize|->Result<Vec<Fr>,String>{
            if slot>=1<<SLOT_BITS{return Err("sample source slot outside input".into());}
            match slot{
                1=>Ok(source_local_input.clone()),
                DAA_RESULT_SLOT=>Ok(local_input.clone()),
                _=>Ok(vec![Fr::zero();INPUT_WIDTH]),
            }
        };
        let mut sample_edge_hasher=Blake2bVar::new(32).unwrap();
        sample_edge_hasher.update(b"nipopow-v2-selected-three-family-production-edges-v1");
        for edge in &sampled{
            for value in [edge.source_slot,edge.family_row,edge.term.row,
                edge.term.gate.left,edge.term.gate.right]{
                sample_edge_hasher.update(&(value as u64).to_le_bytes());
            }
            for coefficient in [edge.term.gate.c0,edge.term.gate.c1,
                edge.term.gate.c2,edge.term.gate.c3]{
                let mut bytes=Vec::new();coefficient.serialize_compressed(&mut bytes).unwrap();
                sample_edge_hasher.update(&bytes);
            }
        }
        let mut sample_edge_digest=[0u8;32];
        sample_edge_hasher.finalize_variable(&mut sample_edge_digest).unwrap();
        fn bind_production_sample(transcript:&mut crate::transcript::Transcript,digest:&[u8;32]){
            transcript.append_bytes(b"edge-sample-profile",
                b"selected-daa-boundary-blake-core-six-terms-production-wires-v1");
            transcript.append_bytes(b"edge-sample-blake2b256",digest);
            transcript.append_u64(b"edge-sample-count",6);
            transcript.append_u64(b"slot-bits",SLOT_BITS as u64);
            transcript.append_u64(b"base-row-bits",BASE_ROW_BITS as u64);
            transcript.append_u64(b"family-bits",FAMILY_BITS as u64);
            transcript.append_u64(b"input-bits-per-slot",(INPUT_BITS-SLOT_BITS) as u64);
            transcript.append_u64(b"flattened-input-bits",INPUT_BITS as u64);
        }
        let domain=b"nipopow-v2-selected-three-family-production-geometry-gkr-v1";
        let mut prover_transcript=crate::transcript::Transcript::new(domain);
        let (proof,claim,_,_)=crate::sparse_stream_roster::prove_edge_terms(
            INPUT_BITS-SLOT_BITS,SLOT_BITS,BASE_ROW_BITS,FAMILY_BITS,&MEMBER_ROW_BITS,
            visit_full,load_full,&mut prover_transcript,
            |transcript|bind_production_sample(transcript,&sample_edge_digest),
            |r,u,v|callback_coefficients(&sampled,r,u,v),
        ).unwrap();
        assert_eq!(proof.layers.len(),1);
        assert_eq!(claim.point.len(),INPUT_BITS);
        let mut verifier_transcript=crate::transcript::Transcript::new(domain);
        let verified=crate::gkr::verify_with_wiring(
            &[INPUT_BITS],
            1usize<<(BASE_ROW_BITS+SLOT_BITS+FAMILY_BITS),
            &proof,&mut verifier_transcript,
            |transcript|bind_production_sample(transcript,&sample_edge_digest),
            |_,r,u,v|explicit_coefficients(&sampled,r,u,v)
                .map_err(|_|crate::gkr::GkrError::PointDimension),
        ).unwrap();
        assert_eq!(verified,claim,
            "independent three-family GKR verification must reproduce the producer claim");
        let transcript_ledger=|t:&crate::transcript::Transcript|
            (t.challenges(),t.raw_queries(),t.bytes_absorbed());
        assert_eq!(transcript_ledger(&prover_transcript),transcript_ledger(&verifier_transcript),
            "sampled real GKR prover/verifier transcripts must agree");
    }

    /// Evaluate the complete three-family relation at a GKR wiring point.
    /// The verifier expands local templates and the resident DAA oracle directly;
    /// the prover callback replays production emitters and the global row mapper.
    fn retained_three_family_wiring(daa:&MatureDaaProofEdgeSource<'_>,
        daa_oracle:&[crate::sparse_stream_roster::EdgeTerm],boundary:&crate::segment_relation::Joined,
        released:&[std::ops::Range<usize>],r:&[Fr],u:&[Fr],v:&[Fr],independent:bool)
        ->Result<[Fr;4],String>{
        use crate::sparse_stream_roster::EdgeTerm;
        const MEMBER_BITS:[usize;3]=[17,19,20];
        if r.len()!=26||u.len()!=24||v.len()!=24||daa.result_slot!=9
            ||released!=[348_440..356_632]{
            return Err("retained three-family wiring dimensions or release changed".into());
        }
        let tables=|point:&[Fr]|point.chunks(8).map(|chunk|{
            if independent{
                (0..1usize<<chunk.len()).map(|index|brute_eq_weight(chunk,index)).collect::<Vec<_>>()
            }else{crate::gkr::eq_weights(chunk)}
        }).collect::<Vec<_>>();
        let rt=tables(r);let ut=tables(u);let vt=tables(v);
        let lookup=|tables:&[Vec<Fr>],index:usize|tables.iter().enumerate()
            .fold(Fr::one(),|z,(chunk,table)|z*table[(index>>(8*chunk))&(table.len()-1)]);
        let mut out=[Fr::zero();4];
        let mut add=|edge:EdgeTerm|->Result<(),String>{
            let family=edge.family_row>>20;let local=edge.family_row&((1<<20)-1);
            let gate=&edge.term.gate;
            if family>=3||local>=1<<MEMBER_BITS[family]||edge.term.row!=local
                ||edge.source_slot>=16||gate.left>=1<<24||gate.right>=1<<24{
                return Err("retained three-family wiring edge outside allocation".into());
            }
            let row=if independent{
                (family<<24)|(edge.source_slot<<MEMBER_BITS[family])|local
            }else{
                crate::sparse_stream_roster::global_edge_row(edge.source_slot,
                    edge.family_row,4,20,2,&MEMBER_BITS)?
            };
            let weight=lookup(&rt,row)*lookup(&ut,gate.left)*lookup(&vt,gate.right);
            for (sum,coefficient) in out.iter_mut().zip([gate.c0,gate.c1,gate.c2,gate.c3]){
                *sum+=weight*coefficient;
            }
            Ok(())
        };
        if independent{
            for edge in daa_oracle{add(edge.clone())?;}
            for term in &boundary.boundary.terms{
                if released[0].contains(&term.row){continue;}
                let mut term=term.clone();term.gate.left+=9*work_tree_layout::WIDTH;
                term.gate.right+=9*work_tree_layout::WIDTH;
                add(EdgeTerm{source_slot:9,family_row:(1<<20)|term.row,term})?;
            }
            for copy in 0..8{
                for base in boundary.core4.terms.iter().filter(|term|term.row<1<<17){
                    let mut term=base.clone();term.row+=copy*(1<<17);
                    let offset=9*work_tree_layout::WIDTH+copy*crate::header_hash::CORE_WIDTH;
                    term.gate.left+=offset;term.gate.right+=offset;
                    add(EdgeTerm{source_slot:9,family_row:(2<<20)|term.row,term})?;
                }
            }
        }else{
            daa.emit_all(&mut add)?;
            crate::segment_relation::emit_boundary_edges_for_slot(boundary,9,released,&mut add)?;
            crate::segment_relation::CoreEdgeSource::new(boundary)?.emit_for_slot(9,&mut add)?;
        }
        Ok(out)
    }

    /// Count the complete producer composition before paying for GKR replays.
    /// No combined edge roster or full field-valued history witness is retained.
    fn diagnose_retained_three_family_stream(daa:&MatureDaaProofEdgeSource<'_>,
        daa_oracle:&[crate::sparse_stream_roster::EdgeTerm],source:&crate::packed::PackedFile,
        setup_id:&[u8;32],commitment:&[u8],raws:&[Vec<u8>],digests:&[[u8;32]],
        opening:Option<(&crate::pcs::Setup,&crate::packed::PackedCommitted)>){
        use crate::sparse_stream_roster::EdgeTerm;
        use ark_serialize::CanonicalSerialize;
        const SLOT_BITS:usize=4;
        const BASE_ROW_BITS:usize=20;
        const FAMILY_BITS:usize=2;
        const MEMBER_BITS:[usize;3]=[17,19,20];
        const INPUT_BITS:usize=24;
        const ROW_BITS:usize=BASE_ROW_BITS+SLOT_BITS+FAMILY_BITS;
        assert_eq!(source.input_len(),1<<INPUT_BITS);
        assert_eq!(raws.len(),10);assert_eq!(digests.len(),10);
        assert_eq!(daa.result_slot,9);assert_eq!(daa.projection_slots,10);
        let mut boundary=crate::segment_relation::build(None).unwrap();
        crate::segment_relation::attach_serializer_relation(&mut boundary).unwrap();
        let released=crate::segment_relation::padding_anchor_row_ranges_for_wires(&boundary,
            &[PHASE_BANKS[3].1..PHASE_BANKS[3].1+PHASE_BANKS[3].2]).unwrap();
        assert_eq!(released,vec![348_440..356_632]);
        let core=crate::segment_relation::CoreEdgeSource::new(&boundary).unwrap();
        let started=std::time::Instant::now();
        println!("retained three-family diagnostic starting: expected_terms=[{}, {}, {}], header_families_slot=9, commitment=new_private_digest_assignment, packed_commitment_blake2b256={}, joined_gkr={}",
            daa_oracle.len(),boundary.boundary.terms.len()-8_192,8*172_480,
            compiled_source_digest(commitment),if opening.is_some(){"pending"}else{"not_requested"});
        let target=EdgeTerm{source_slot:daa.result_slot,family_row:daa.x0_aliases[0].row,
            term:daa.x0_aliases[0].clone()};
        let target_row=(target.source_slot<<17)|target.family_row;
        let boolean_bits=|bits:usize,index:usize|(0..bits)
            .map(|bit|Fr::from(((index>>bit)&1) as u64)).collect::<Vec<_>>();
        let boolean_r=boolean_bits(ROW_BITS,target_row);
        let boolean_u=boolean_bits(INPUT_BITS,target.term.gate.left);
        let boolean_v=boolean_bits(INPUT_BITS,target.term.gate.right);
        let r=(0..ROW_BITS).map(|i|Fr::from(3+2*i as u64)).collect::<Vec<_>>();
        let u=(0..INPUT_BITS).map(|i|Fr::from(5+3*i as u64)).collect::<Vec<_>>();
        let v=(0..INPUT_BITS).map(|i|Fr::from(7+5*i as u64)).collect::<Vec<_>>();
        // Callback uses factored tensor coordinates and ordinary equality tables.
        let local_rows=MEMBER_BITS.map(|bits|crate::gkr::eq_weights(&r[..bits]));
        let row_scales:Vec<Vec<Fr>>=MEMBER_BITS.iter().enumerate().map(|(family,&bits)|{
            (0..16).map(|slot|crate::work_tree_wiring::eq_index(&r[24..],family)
                *crate::work_tree_wiring::eq_index(&r[bits..bits+4],slot)
                *r[bits+4..24].iter().fold(Fr::one(),|z,x|z*(Fr::one()-x)))
                .collect()
        }).collect();
        let u_local=crate::gkr::eq_weights(&u[..20]);
        let v_local=crate::gkr::eq_weights(&v[..20]);
        let u_slots=crate::gkr::eq_weights(&u[20..]);
        let v_slots=crate::gkr::eq_weights(&v[20..]);
        // Independent expansion uses full integer row labels and bit-loop
        // equality products. Byte tables only reuse those exact products.
        let explicit_tables=|point:&[Fr]|point.chunks(8).map(|chunk|
            (0..1usize<<chunk.len()).map(|index|brute_eq_weight(chunk,index))
                .collect::<Vec<_>>()).collect::<Vec<_>>();
        let explicit_r=explicit_tables(&r);
        let explicit_u=explicit_tables(&u);
        let explicit_v=explicit_tables(&v);
        let lookup=|tables:&[Vec<Fr>],index:usize|tables.iter().enumerate()
            .fold(Fr::one(),|z,(chunk,table)|z*table[(index>>(8*chunk))&(table.len()-1)]);
        let coefficients=|edge:&EdgeTerm,independent:bool|->([Fr;4],[Fr;4]){
            let family=edge.family_row>>BASE_ROW_BITS;
            let local=edge.family_row&((1<<BASE_ROW_BITS)-1);
            assert!(family<3&&local<1<<MEMBER_BITS[family]&&edge.source_slot<16);
            assert_eq!(edge.term.row,local);
            let gate=&edge.term.gate;
            assert!(gate.left<1<<INPUT_BITS&&gate.right<1<<INPUT_BITS);
            let row=if independent{
                (family<<(BASE_ROW_BITS+SLOT_BITS))|(edge.source_slot<<MEMBER_BITS[family])|local
            }else{
                crate::sparse_stream_roster::global_edge_row(edge.source_slot,edge.family_row,
                    SLOT_BITS,BASE_ROW_BITS,FAMILY_BITS,&MEMBER_BITS).unwrap()
            };
            let weight=if independent{
                lookup(&explicit_r,row)*lookup(&explicit_u,gate.left)*lookup(&explicit_v,gate.right)
            }else{
                local_rows[family][local]*row_scales[family][edge.source_slot]
                    *u_local[gate.left%work_tree_layout::WIDTH]*u_slots[gate.left/work_tree_layout::WIDTH]
                    *v_local[gate.right%work_tree_layout::WIDTH]*v_slots[gate.right/work_tree_layout::WIDTH]
            };
            let cs=[gate.c0,gate.c1,gate.c2,gate.c3];
            let boolean_weight=if independent{
                if row==target_row&&gate.left==target.term.gate.left&&gate.right==target.term.gate.right{
                    Fr::one()
                }else{Fr::zero()}
            }else if gate.left!=target.term.gate.left||gate.right!=target.term.gate.right{
                // Exact Boolean endpoint selection avoids evaluating row
                // products for the millions of edges at other wire labels.
                Fr::zero()
            }else{
                crate::work_tree_wiring::eq_index(&boolean_r[..MEMBER_BITS[family]],local)
                    *crate::work_tree_wiring::eq_index(&boolean_r[MEMBER_BITS[family]..MEMBER_BITS[family]+4],edge.source_slot)
                    *boolean_r[MEMBER_BITS[family]+4..24].iter().fold(Fr::one(),|z,x|z*(Fr::one()-x))
                    *crate::work_tree_wiring::eq_index(&boolean_r[24..],family)
                    *crate::work_tree_wiring::eq_index(&boolean_u,gate.left)
                    *crate::work_tree_wiring::eq_index(&boolean_v,gate.right)
            };
            (cs.map(|c|weight*c),cs.map(|c|boolean_weight*c))
        };
        struct Inventory{
            counts:[[usize;16];3],hashes:[Blake2bVar;3],sum:[Fr;4],boolean:[Fr;4],
            scalar_bytes:Vec<u8>,
            // Omission, family-tag replacement and source-slot replacement.
            mutants:[[Fr;4];3],boolean_mutants:[[Fr;4];3],targets:usize,
        }
        let inventory=||Inventory{counts:[[0;16];3],hashes:std::array::from_fn(|family|{
            let mut h=Blake2bVar::new(32).unwrap();
            h.update(b"retained-three-family-canonical-stream-v1");
            h.update(&(family as u64).to_le_bytes());h
        }),sum:[Fr::zero();4],boolean:[Fr::zero();4],mutants:[[Fr::zero();4];3],
            boolean_mutants:[[Fr::zero();4];3],targets:0,scalar_bytes:Vec::with_capacity(32)};
        let observe=|state:&mut Inventory,edge:EdgeTerm,independent:bool|{
            let (values,boolean)=coefficients(&edge,independent);
            let family=edge.family_row>>BASE_ROW_BITS;
            state.counts[family][edge.source_slot]+=1;
            let h=&mut state.hashes[family];
            for label in [edge.source_slot,edge.family_row,edge.term.row,edge.term.gate.left,edge.term.gate.right]{
                h.update(&(label as u64).to_le_bytes());
            }
            for c in [edge.term.gate.c0,edge.term.gate.c1,edge.term.gate.c2,edge.term.gate.c3]{
                c.serialize_compressed(&mut state.scalar_bytes).unwrap();
                h.update(&state.scalar_bytes);state.scalar_bytes.clear();
            }
            let selected=edge.source_slot==target.source_slot&&edge.family_row==target.family_row
                &&edge.term==target.term;
            let mut variants=[(values,boolean);3];
            if selected{
                state.targets+=1;
                variants[0]=([Fr::zero();4],[Fr::zero();4]);
                let mut tag=edge.clone();tag.family_row|=1<<BASE_ROW_BITS;
                variants[1]=coefficients(&tag,independent);
                let mut slot=edge.clone();slot.source_slot-=1;
                variants[2]=coefficients(&slot,independent);
            }
            for i in 0..4{
                state.sum[i]+=values[i];state.boolean[i]+=boolean[i];
                for mutant in 0..3{
                    state.mutants[mutant][i]+=variants[mutant].0[i];
                    state.boolean_mutants[mutant][i]+=variants[mutant].1[i];
                }
            }
        };
        let mut actual=inventory();
        daa.emit_all(&mut |edge|{observe(&mut actual,edge,false);Ok(())}).unwrap();
        for slot in [daa.result_slot]{
            let input=read_packed_hash_slot(source,slot,16).unwrap();
            let mut rows=vec![Fr::zero();boundary.boundary.row_count];
            let mut accept=|edge:EdgeTerm|{
                let mut local=edge.term.gate.clone();
                local.left-=slot*work_tree_layout::WIDTH;local.right-=slot*work_tree_layout::WIDTH;
                rows[edge.term.row]+=local.evaluate(&input);
                observe(&mut actual,edge,false);Ok(())
            };
            let omitted=crate::segment_relation::emit_boundary_edges_for_slot(&boundary,slot,
                if slot==9{&released}else{&[]},&mut accept).unwrap();
            assert_eq!(omitted,if slot==9{8_192}else{0});
            drop(accept);
            assert!(rows.iter().all(Zero::is_zero),"private boundary rejects packed slot {slot}");
            let mut rows=vec![Fr::zero();1<<20];
            core.emit_for_slot(slot,&mut |edge|{
                let mut local=edge.term.gate.clone();
                local.left-=slot*work_tree_layout::WIDTH;local.right-=slot*work_tree_layout::WIDTH;
                rows[edge.term.row]+=local.evaluate(&input);
                observe(&mut actual,edge,false);Ok(())
            }).unwrap();
            assert!(rows.iter().all(Zero::is_zero),"BLAKE core rejects packed slot {slot}");
        }
        let mut expected=inventory();
        for edge in daa_oracle{observe(&mut expected,edge.clone(),true);}
        // Expand producer templates directly, without calling any edge emitter
        // or global-row helper. Retain only the already compiled local sources.
        for slot in [daa.result_slot]{
            for term in &boundary.boundary.terms{
                if slot==9&&released[0].contains(&term.row){continue;}
                let mut term=term.clone();term.gate.left+=slot*work_tree_layout::WIDTH;
                term.gate.right+=slot*work_tree_layout::WIDTH;
                observe(&mut expected,EdgeTerm{source_slot:slot,family_row:(1<<20)|term.row,term},true);
            }
            for copy in 0..8{
                for base in boundary.core4.terms.iter().filter(|term|term.row<1<<17){
                    let mut term=base.clone();term.row+=copy*(1<<17);
                    let offset=slot*work_tree_layout::WIDTH+copy*crate::header_hash::CORE_WIDTH;
                    term.gate.left+=offset;term.gate.right+=offset;
                    observe(&mut expected,EdgeTerm{source_slot:slot,family_row:(2<<20)|term.row,term},true);
                }
            }
        }
        assert_eq!(actual.counts,expected.counts);assert_eq!(actual.sum,expected.sum);
        assert_eq!(actual.boolean,expected.boolean);assert_eq!(actual.targets,1);
        assert_eq!(expected.targets,1);
        assert_eq!(actual.boolean,[Fr::zero(),Fr::one(),-Fr::one(),Fr::zero()]);
        assert_eq!(actual.mutants,expected.mutants);
        assert_eq!(actual.boolean_mutants,expected.boolean_mutants);
        for mutant in 0..3{
            assert_ne!(actual.mutants[mutant],actual.sum,"isolated stream mutant {mutant}");
            assert_eq!(actual.boolean_mutants[mutant],[Fr::zero();4]);
        }
        let counts=actual.counts;
        assert_eq!(counts[0].iter().sum::<usize>(),daa_oracle.len());
        assert_eq!(counts[1].iter().sum::<usize>(),473_363-8_192);
        assert_eq!(counts[2].iter().sum::<usize>(),8*172_480);
        assert!(counts[1].iter().enumerate().all(|(slot,count)|slot==9||*count==0));
        assert!(counts[2].iter().enumerate().all(|(slot,count)|slot==9||*count==0));
        let finish=|hashes:[Blake2bVar;3]|hashes.map(|h|{
            let mut digest=[0u8;32];h.finalize_variable(&mut digest).unwrap();digest
        });
        let stream_digests=finish(actual.hashes);
        assert_eq!(stream_digests,finish(expected.hashes),"canonical streams differ from explicit expansion");
        let bind=|t:&mut crate::transcript::Transcript,bound_commitment:&[u8]|{
            t.append_bytes(b"scope",b"retained spaced pre-EIP-37 samples 1,129,...,1025; synthetic computed child 1153; no parent continuity, root/history completeness, activation applicability or historical validity");
            t.append_bytes(b"family-scope",b"complete ten-slot DAA/projection; complete private boundary and eight BLAKE cores only at result slot 9; other headers are not authenticated by this stream");
            for (label,value) in [(b"input-bits".as_slice(),INPUT_BITS),(b"slot-bits",SLOT_BITS),
                (b"base-row-bits",BASE_ROW_BITS),(b"family-bits",FAMILY_BITS)]{
                t.append_u64(label,value as u64);
            }
            for family in 0..3{
                t.append_u64(b"family",family as u64);t.append_u64(b"member-row-bits",MEMBER_BITS[family] as u64);
                for slot in 0..16{
                    t.append_u64(b"source-slot",slot as u64);t.append_u64(b"edge-count",counts[family][slot] as u64);
                }
                t.append_bytes(b"canonical-stream-blake2b256",&stream_digests[family]);
            }
            for slot in 0..10{
                t.append_u64(b"header-slot",slot as u64);t.append_u64(b"encoded-length",raws[slot].len() as u64);
                t.append_bytes(b"native-header-digest",&digests[slot]);
            }
            t.append_bytes(b"pcs-setup-id",setup_id);t.append_bytes(b"packed-commitment",bound_commitment);
        };
        let domain=b"retained-three-family-stream-inventory-no-proof-v1";
        let mut transcript=crate::transcript::Transcript::new(domain);bind(&mut transcript,commitment);
        let challenge=transcript.challenge_scalar(b"inventory-binding");
        let mut replay=crate::transcript::Transcript::new(domain);bind(&mut replay,commitment);
        assert_eq!(challenge,replay.challenge_scalar(b"inventory-binding"));
        assert_eq!((transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed()),
            (replay.challenges(),replay.raw_queries(),replay.bytes_absorbed()));
        let mut changed=commitment.to_vec();changed[0]^=1;
        let mut wrong=crate::transcript::Transcript::new(domain);bind(&mut wrong,&changed);
        assert_ne!(challenge,wrong.challenge_scalar(b"inventory-binding"));
        println!("retained three-family stream inventory: counts={counts:?}, digests={:?}, coefficient_differential=pass, omission_tag_slot_negatives=pass, packed_boundary_core_residuals=zero, transcript_binding=pass, commitment=new_private_digest_assignment, packed_commitment_blake2b256={}, inventory_ms={}, gkr_proof=not_run, pcs_opening=not_run",
            stream_digests.map(|digest|hex(&digest)),compiled_source_digest(commitment),
            started.elapsed().as_millis());
        if let Some((setup,committed))=opening{
            assert_eq!(&setup.id,setup_id);
            assert_eq!(crate::pcs::encode_commitment(&committed.commitment).unwrap(),commitment);
            // The diagnostic tables have completed their differential. Release
            // them before the streamed producer allocates its per-slot vectors.
            drop(observe);drop(coefficients);drop(local_rows);drop(row_scales);
            drop(u_local);drop(v_local);drop(u_slots);drop(v_slots);
            drop(explicit_r);drop(explicit_u);drop(explicit_v);
            let domain=b"retained-three-family-slot9-gkr-dory-opened-v1";
            const CACHE_BASELINE_BYTES:usize=448*1024*1024;
            println!("retained three-family phase=gkr_baseline_start, cache_limit_mib=448");
            let mut baseline_prover=crate::transcript::Transcript::new(domain);
            let baseline_started=std::time::Instant::now();
            let (baseline_proof,baseline_claim,baseline_incremental_u,baseline_incremental_v)=crate::sparse_stream_roster::prove_edge_terms_with_cache_limit_for_test(
                20,4,20,2,&MEMBER_BITS,CACHE_BASELINE_BYTES,
                |left_endpoint,slot,sink|{
                    daa.emit_endpoint(left_endpoint,slot,sink)?;
                    if slot==9{
                        crate::segment_relation::emit_boundary_edges_for_slot(&boundary,slot,&released,sink)?;
                        core.emit_for_slot(slot,sink)?;
                    }
                    Ok(())
                },
                |slot|read_packed_hash_slot(source,slot,16),&mut baseline_prover,
                |t|bind(t,commitment),
                |r,u,v|retained_three_family_wiring(daa,daa_oracle,&boundary,&released,r,u,v,false),
            ).unwrap();
            let baseline_prover_ms=baseline_started.elapsed().as_millis();
            assert_eq!((baseline_incremental_u,baseline_incremental_v),(false,false),
                "the 448 MiB runtime baseline must use its established fallback");
            println!("retained three-family phase=gkr_candidate_start, cache_limit_mib={}, baseline_prover_ms={baseline_prover_ms}",
                crate::sparse_stream_roster::MAX_EDGE_INCREMENTAL_LOCAL_BYTES/(1024*1024));
            let mut prover=crate::transcript::Transcript::new(domain);
            let prove_started=std::time::Instant::now();
            let (proof,claim,incremental_u,incremental_v)=crate::sparse_stream_roster::prove_edge_terms(
                20,4,20,2,&MEMBER_BITS,
                |left_endpoint,slot,sink|{
                    daa.emit_endpoint(left_endpoint,slot,sink)?;
                    if slot==9{
                        crate::segment_relation::emit_boundary_edges_for_slot(&boundary,slot,&released,sink)?;
                        core.emit_for_slot(slot,sink)?;
                    }
                    Ok(())
                },
                |slot|read_packed_hash_slot(source,slot,16),&mut prover,
                |t|bind(t,commitment),
                |r,u,v|retained_three_family_wiring(daa,daa_oracle,&boundary,&released,r,u,v,false),
            ).unwrap();
            let prover_ms=prove_started.elapsed().as_millis();
            println!("retained three-family phase=gkr_candidate_done, candidate_prover_ms={prover_ms}, incremental_u={incremental_u}, incremental_v={incremental_v}");
            assert_eq!(crate::gkr::encode_proof(&proof).unwrap(),crate::gkr::encode_proof(&baseline_proof).unwrap(),
                "1.25 GiB candidate must preserve canonical GKR proof bytes");
            assert_eq!(claim,baseline_claim,"1.25 GiB candidate must preserve the GKR claim");
            let transcript_ledger=|t:&crate::transcript::Transcript|
                (t.challenges(),t.raw_queries(),t.bytes_absorbed());
            assert_eq!(transcript_ledger(&prover),transcript_ledger(&baseline_prover),
                "1.25 GiB candidate must preserve the GKR transcript ledger");
            assert_eq!(prover.clone().challenge_scalar(b"retained-three-family-continuation"),
                baseline_prover.clone().challenge_scalar(b"retained-three-family-continuation"),
                "1.25 GiB candidate must preserve the GKR continuation challenge");
            assert_eq!((incremental_u,incremental_v),(true,true),
                "1.25 GiB candidate must activate both incremental phases");
            assert_eq!(proof.layers.len(),1);assert_eq!(claim.point.len(),24);
            assert_eq!(source.evaluate(&claim.point).unwrap(),claim.value,
                "joined GKR claim must evaluate against its dedicated packed witness");
            let gkr_bytes=crate::gkr::encode_proof(&proof).unwrap();
            let decoded=crate::gkr::decode_dimensions(&[24],&gkr_bytes).unwrap();
            assert_eq!(decoded,proof);
            let mut verifier=crate::transcript::Transcript::new(domain);
            let verify_started=std::time::Instant::now();
            let verified=crate::gkr::verify_with_wiring(&[24],1<<26,&decoded,&mut verifier,
                |t|bind(t,commitment),
                |_,r,u,v|retained_three_family_wiring(daa,daa_oracle,&boundary,&released,r,u,v,true)
                    .map_err(|_|crate::gkr::GkrError::PointDimension)).unwrap();
            let verifier_ms=verify_started.elapsed().as_millis();
            assert_eq!(verified,claim,"independent full-family GKR verifier claim differs");
            let ledger=|t:&crate::transcript::Transcript|
                (t.challenges(),t.raw_queries(),t.bytes_absorbed());
            assert_eq!(ledger(&prover),ledger(&verifier));
            let continuation=|t:&crate::transcript::Transcript|t.clone()
                .challenge_scalar(b"retained-three-family-continuation");
            assert_eq!(continuation(&prover),continuation(&verifier));
            // Continue the exact GKR transcripts into the opening statement;
            // no unrelated transcript or public-digest commitment is substituted.
            let pcs_started=std::time::Instant::now();
            println!("retained three-family phase=pcs_opening_start, gkr_verifier_ms={verifier_ms}");
            let opening_proof=crate::packed::open(committed,source,&claim.point,setup,&mut prover).unwrap();
            let pcs_prover_ms=pcs_started.elapsed().as_millis();
            let pcs_bytes=crate::pcs::encode_proof(&opening_proof).unwrap();
            let decoded_opening=crate::pcs::decode_proof(&pcs_bytes,24).unwrap();
            let pcs_verify_started=std::time::Instant::now();
            crate::pcs::verify(committed.commitment,verified.value,&verified.point,
                &decoded_opening,setup,&mut verifier).unwrap();
            let pcs_verifier_ms=pcs_verify_started.elapsed().as_millis();
            assert_eq!(ledger(&prover),ledger(&verifier));
            assert_eq!(continuation(&prover),continuation(&verifier));
            println!("retained three-family GKR-Dory opened: header_families_slot=9, gkr_bytes={}, pcs_bytes={}, total_proof_bytes={}, baseline_448_prover_ms={}, candidate_default_limit_mib={}, candidate_prover_ms={}, gkr_verifier_ms={}, pcs_prover_ms={}, pcs_verifier_ms={}, incremental_u={}, incremental_v={}, packed_commitment_blake2b256={}, result=pass, full_history=not_claimed, EIP37_applicability=not_claimed, authenticated_ancestry=not_claimed",
                gkr_bytes.len(),pcs_bytes.len(),gkr_bytes.len()+pcs_bytes.len(),baseline_prover_ms,
                crate::sparse_stream_roster::MAX_EDGE_INCREMENTAL_LOCAL_BYTES/(1024*1024),prover_ms,
                verifier_ms,pcs_prover_ms,pcs_verifier_ms,incremental_u,incremental_v,
                compiled_source_digest(commitment));
        }
    }

    #[test]
    fn mature_a1_external_fields_alias_retained_mainnet_serializer_slots(){
        retained_mainnet_serializer_fixture(false,false);
    }

    #[test]
    #[ignore = "wiring-only differential for the current ten-slot DAA fixture; no GKR, PCS or historical coverage"]
    fn retained_daa_wiring_factorizes_projection_and_cross_slot_aliases(){
        retained_mainnet_serializer_fixture_mode(false,false,true);
    }

    fn diagnose_retained_daa_factorization(daa:&MatureDaaProofEdgeSource<'_>,
        oracle:&[crate::sparse_stream_roster::EdgeTerm]){
        assert_eq!(daa.result_slot,9);assert_eq!(daa.projection_slots,10);
        assert_eq!(daa.projection.terms.len(),2_379);
        assert_eq!(daa.projection_residual_rows,1_175);
        assert_eq!(daa.projection_aux_end-daa.projection_aux_start,384);
        assert_eq!(daa.bank_slack_rows,16_384);
        assert_eq!((daa.aliases.len(),daa.child_aliases.len(),daa.x0_aliases.len()),(832,32,32));
        assert_eq!(oracle.len(),daa.original.terms.len()+41_070);
        let target=&daa.x0_aliases[0];
        let width=work_tree_layout::WIDTH;
        assert_eq!(width,1<<20);
        assert_eq!((target.gate.left/width,target.gate.right/width),(9,1));
        let coefficients=|g:&Gate|[g.c0,g.c1,g.c2,g.c3];
        let tables=|point:&[Fr],independent:bool|point.chunks(8).map(|chunk|{
            if independent{(0..1usize<<chunk.len()).map(|i|brute_eq_weight(chunk,i)).collect()}
            else{crate::gkr::eq_weights(chunk)}
        }).collect::<Vec<Vec<Fr>>>();
        let lookup=|tables:&[Vec<Fr>],index:usize|tables.iter().enumerate()
            .fold(Fr::one(),|z,(chunk,table)|z*table[(index>>(8*chunk))&(table.len()-1)]);
        // The reference uses full integer indices and independently computed
        // equality tables. It does not split slots or call the global-row mapper.
        let explicit=|r:&[Fr],u:&[Fr],v:&[Fr],stream:bool,mutant:bool|{
            let rt=tables(r,true);let ut=tables(u,true);let vt=tables(v,true);
            let mut out=[Fr::zero();4];
            let mut add=|edge:crate::sparse_stream_roster::EdgeTerm|->Result<(),String>{
                assert_eq!(edge.term.row,edge.family_row);
                assert!(edge.family_row<1<<17&&edge.source_slot<16);
                let gate=&edge.term.gate;
                let right=if mutant&&edge.source_slot==9&&edge.family_row==target.row{
                    assert_eq!(edge.term,*target);gate.right+width
                }else{gate.right};
                let row=(edge.source_slot<<17)|edge.family_row;
                let weight=lookup(&rt,row)*lookup(&ut,gate.left)*lookup(&vt,right);
                for (sum,c) in out.iter_mut().zip(coefficients(gate)){*sum+=weight*c;}
                Ok(())
            };
            if stream{daa.emit_all(&mut add).unwrap();}
            else{for edge in oracle{add(edge.clone()).unwrap();}}
            out
        };
        // Evaluate each local template once. The arithmetic template still has
        // its original term cost; only repeated projection expansion is removed.
        let factored=|r:&[Fr],u:&[Fr],v:&[Fr],mutant:bool|{
            assert_eq!((r.len(),u.len(),v.len()),(26,24,24));
            let rt=tables(&r[..17],false);let ut=tables(&u[..20],false);
            let vt=tables(&v[..20],false);
            let rs=crate::gkr::eq_weights(&r[17..21]);
            let us=crate::gkr::eq_weights(&u[20..24]);
            let vs=crate::gkr::eq_weights(&v[20..24]);
            let z=r[21..26].iter().fold(Fr::one(),|a,x|a*(Fr::one()-x));
            let singleton=rs[9]*us[9]*vs[9];
            let projection_factor=(0..10).fold(Fr::zero(),|a,s|a+rs[s]*us[s]*vs[s]);
            let mut out=[Fr::zero();4];
            let mut add=|row:usize,left:usize,right:usize,c:[Fr;4],factor:Fr|{
                assert!(row<1<<17&&left<width&&right<width);
                let weight=lookup(&rt,row)*lookup(&ut,left)*lookup(&vt,right)*factor;
                for (sum,c) in out.iter_mut().zip(c){*sum+=weight*c;}
            };
            for term in &daa.original.terms{
                let g=&term.gate;
                let left_active=!g.c1.is_zero()||!g.c3.is_zero();
                let right_active=!g.c2.is_zero()||!g.c3.is_zero();
                let left=if left_active{daa.wire_map[g.left]}
                    else if right_active{daa.wire_map[g.right]}else{PHASE_BANKS[0].1};
                let right=if right_active{daa.wire_map[g.right]}else{left};
                add(term.row,left,right,coefficients(g),singleton);
            }
            let mut slack=0;
            for ((_,start,bank_width),used) in PHASE_BANKS.into_iter().zip(daa.used){
                for wire in start+used..start+bank_width{
                    add(daa.daa_row_start+slack,wire,wire,
                        [Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()],singleton);
                    slack+=1;
                }
            }
            assert_eq!(slack,daa.bank_slack_rows);
            for term in daa.child_aliases{
                assert_eq!((term.gate.left/width,term.gate.right/width),(9,9));
                add(term.row,term.gate.left%width,term.gate.right%width,
                    coefficients(&term.gate),singleton);
            }
            let projection_wire=|wire:usize|if wire<daa.projection_aux_start{
                daa.serializer_offset+wire
            }else{
                assert!(wire<daa.projection_aux_end);
                daa.projection_aux_bank_start+wire-daa.projection_aux_start
            };
            for term in &daa.projection.terms{
                add(daa.projection_row_start+term.row,projection_wire(term.gate.left),
                    projection_wire(term.gate.right),coefficients(&term.gate),projection_factor);
            }
            for term in daa.aliases.iter().chain(daa.x0_aliases){
                assert_eq!(term.gate.left/width,9);
                let mut right_slot=term.gate.right/width;
                if mutant&&term.row==target.row{assert_eq!(right_slot,1);right_slot=2;}
                add(term.row,term.gate.left%width,term.gate.right%width,
                    coefficients(&term.gate),rs[9]*us[9]*vs[right_slot]);
            }
            out.map(|value|value*z)
        };
        let check=|r:&[Fr],u:&[Fr],v:&[Fr]|{
            let expected=explicit(r,u,v,false,false);
            assert_eq!(explicit(r,u,v,true,false),expected,"emitter versus resident oracle");
            assert_eq!(factored(r,u,v,false),expected,"factored DAA wiring");
            expected
        };
        for seed in [3u64,101]{
            let point=|bits:usize,offset:u64|(0..bits)
                .map(|i|Fr::from(seed+offset+7*i as u64)).collect::<Vec<_>>();
            let (r,u,v)=(point(26,0),point(24,211),point(24,433));
            let expected=check(&r,&u,&v);
            let changed=explicit(&r,&u,&v,false,true);
            assert_eq!(factored(&r,&u,&v,true),changed);
            assert_ne!(changed,expected,"isolated x0 right-slot mutant");
        }
        let r=bool_point(26,(9<<17)|target.row);
        let u=bool_point(24,target.gate.left);let v=bool_point(24,target.gate.right);
        assert_eq!(check(&r,&u,&v),[Fr::zero(),Fr::one(),-Fr::one(),Fr::zero()]);
        assert_eq!(explicit(&r,&u,&v,false,true),[Fr::zero();4]);
        assert_eq!(factored(&r,&u,&v,true),[Fr::zero();4]);
        let projection=&daa.projection.terms[0];
        for slot in [0,9,10]{
            let r=bool_point(26,(slot<<17)|(daa.projection_row_start+projection.row));
            let wire=|w|if w<daa.projection_aux_start{daa.serializer_offset+w}
                else{daa.projection_aux_bank_start+w-daa.projection_aux_start};
            let u=bool_point(24,slot*width+wire(projection.gate.left));
            let v=bool_point(24,slot*width+wire(projection.gate.right));
            assert_eq!(check(&r,&u,&v),if slot<10{coefficients(&projection.gate)}else{[Fr::zero();4]});
        }
        for bit in 21..26{
            let mut padding=r.clone();padding[bit]=Fr::one();
            assert_eq!(check(&padding,&u,&v),[Fr::zero();4],"DAA row padding bit {bit}");
        }
        println!("retained DAA wiring-only differential: original_terms={}, oracle_terms={}, projection_template_terms=2379, projection_copies=10, projection_terms_saved=21411, nonboolean_points=2, x0_slots=9/9/1, isolated_x0_right_slot_mutant=rejected; no GKR, PCS, runtime benchmark or historical coverage",
            daa.original.terms.len(),oracle.len());
    }

    #[test]
    #[ignore = "full retained-header three-family stream inventory and coefficient differential"]
    fn retained_header_three_family_stream_inventory(){
        retained_mainnet_serializer_fixture(true,false);
    }

    #[test]
    #[ignore = "complete retained DAA/projection plus slot9 private boundary and BLAKE GKR-Dory opening"]
    fn retained_header_three_family_gkr_opened(){
        retained_mainnet_serializer_fixture(true,true);
    }

    fn retained_mainnet_serializer_fixture(inventory_only:bool,opened:bool){
        retained_mainnet_serializer_fixture_mode(inventory_only,opened,false);
    }

    fn retained_mainnet_serializer_fixture_mode(inventory_only:bool,opened:bool,wiring_only:bool){
        assert!(!opened||inventory_only);
        use ergo_header_core::Header;
        use num_bigint::{BigInt,Sign};

        const SAMPLE_COUNT:usize=9;
        const SAMPLE_STEP:usize=128;
        const DAA_RESULT_SLOT:usize=SAMPLE_COUNT;
        const BANK_SLACK_ROWS:usize=16_384;
        const PROJECTION_AUX_START:usize=671_744;
        const PROJECTION_AUX_END:usize=688_128;

        // The nine fixture heights are 1, 129, ..., 1025. They exercise the E=128
        // arithmetic shape, but predate EIP-37. The forecast point x0+8E is
        // height 1153; its slot is reserved for the computed child result.
        // This validates field aliases, not EIP activation or DAA applicability.
        let pack:Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
        let encoded=pack["networks"]["mainnet"]["source_headers_hex"].as_array().unwrap();
        let headers=(0..SAMPLE_COUNT).map(|sample|{
            let height=1+sample*SAMPLE_STEP;
            let hex=encoded[height-1].as_str().unwrap();
            let raw=hex.as_bytes().chunks_exact(2).map(|pair|
                u8::from_str_radix(std::str::from_utf8(pair).unwrap(),16).unwrap()).collect::<Vec<_>>();
            let header=Header::decode(&raw,None).unwrap();
            assert_eq!(header.height as usize,height);
            assert_eq!(header.encode().unwrap(),raw);
            header
        }).collect::<Vec<_>>();
        assert!(headers.windows(2).all(|pair|pair[0].timestamp<pair[1].timestamp));
        assert!(headers.last().unwrap().height<descriptor().eip_activation_child as u32);
        let child_height=headers[1].height+8*SAMPLE_STEP as u32;
        assert_eq!(child_height,1153);
        let child_hex=encoded[child_height as usize-1].as_str().unwrap();
        let child_bytes=child_hex.as_bytes().chunks_exact(2).map(|pair|
            u8::from_str_radix(std::str::from_utf8(pair).unwrap(),16).unwrap()).collect::<Vec<_>>();
        let mut child_header=Header::decode(&child_bytes,None).unwrap();
        assert_eq!(child_header.height,child_height);
        assert_eq!(child_header.encode().unwrap(),child_bytes);

        let serializer=crate::serializer::build(None).unwrap();
        let projection=crate::serializer_field_projection::Compiled::build(&serializer).unwrap();
        assert_eq!(serializer.layout.fields.timestamp,std::array::from_fn(|bit|1_042+bit));
        assert_eq!(serializer.layout.fields.n_bits,std::array::from_fn(|bit|1_362+bit));
        let fields=headers.iter().map(crate::serializer::Fields::from_header)
            .collect::<Result<Vec<_>,_>>().unwrap();
        let mut serialized=headers.iter().zip(&fields).map(|(_,field)|serializer.assign(field))
            .collect::<Vec<_>>();
        for assignment in &serialized{
            assert!(circuit_residuals(&serializer.circuit,assignment).iter().all(Zero::is_zero),
                "fixture header does not satisfy the canonical serializer relation");
        }

        let window=WindowInputs{
            nbits:std::array::from_fn(|sample|headers[sample+1].n_bits),
            timestamps:std::array::from_fn(|sample|headers[sample].timestamp),
        };

        // Derive the EIP-shaped result independently, then place those raw
        // compact bits in the serialized child header at x0+8E. The child
        // fixture keeps its source fields but substitutes this computed nBits.
        let x0=headers[1].height;
        let values=std::array::from_fn(|sample|{
            let difficulty=crate::work_tree_work::native_decode(window.nbits[sample]).unwrap();
            let duration=window.timestamps[sample+1]-window.timestamps[sample];
            BigInt::from_biguint(Sign::Plus,difficulty)
                *BigInt::from(120_000u64*Epoch::Eip.length())/BigInt::from(duration)
        });
        let prediction=crate::daa_regression::native_prediction_oracle(x0 as i64,Epoch::Eip,&values).2;
        let last=crate::work_tree_work::native_decode(window.nbits[7]).unwrap();
        let child_numeric=daa_finish::native_finish_oracle(Epoch::Eip,&prediction,&values[7],&last).unwrap();
        let (child_nbits,decoded_child)=daa_finish::native_positive_compact_roundtrip(&child_numeric);
        assert_eq!(decoded_child,child_numeric);
        child_header.n_bits=child_nbits;
        let child_roundtrip=Header::decode(&child_header.encode().unwrap(),None).unwrap();
        assert_eq!(child_roundtrip.n_bits,child_nbits);
        let child_fields=crate::serializer::Fields::from_header(&child_header).unwrap();
        serialized.push(serializer.assign(&child_fields));
        assert!(circuit_residuals(&serializer.circuit,serialized.last().unwrap()).iter().all(Zero::is_zero),
            "computed child header does not satisfy the canonical serializer relation");

        // Count the A1-A4 mature relation plus the child nBits join for this
        // real-field arithmetic fixture; this remains a local composition.
        let composed=daa_finish::compile_finish_with_child(Epoch::Eip,&q(),
            PredictionInput{window,x0},child_nbits,true).unwrap();
        let count=&composed.joined.joined.joined.count;
        assert!(composed.joined.joined.joined.circuit.is_some());
        assert_eq!(count.padded_input_bits,65_536);
        assert_eq!(count.padded_rows,1<<17);
        let a1=&composed.joined.joined.joined;
        assert_eq!(a1.external.len(),8);
        assert_eq!(a1.witness.len(),count.padded_input_bits);
        for sample in 0..8{
            for bit in 0..32{
                assert_eq!(a1.external[sample].nbits[bit],sample*32+bit);
            }
            for bit in 0..64{
                assert_eq!(a1.external[sample].start_timestamp[bit],256+sample*64+bit);
                assert_eq!(a1.external[sample].end_timestamp[bit],256+(sample+1)*64+bit);
            }
        }

        let slots=(SAMPLE_COUNT+1).next_power_of_two();
        let global_input_len=slots*work_tree_layout::WIDTH;
        assert_eq!(slots,16);
        assert_eq!(global_input_len,1<<24);
        let a1_live=composed.joined.joined.increment.before.live_bits;
        let a1_bank_start=PHASE_BANKS[0].1;
        let a1_bank_width=PHASE_BANKS[0].2;
        let serializer_offset=crate::header_hash::SERIALIZER_OFFSET;
        let mut coordinate_values=BTreeMap::<usize,Fr>::new();
        let mut aliases=Vec::<Term>::with_capacity(8*32+9*64);
        let mut add_alias=|daa_wire:usize,header_slot:usize,serializer_wire:usize|{
            assert!(daa_wire<a1_live,"external DAA bit is not in phase A1");
            let daa_local=a1_bank_start+daa_wire;
            let serializer_local=serializer_offset+serializer_wire;
            assert!(daa_local<a1_bank_start+a1_bank_width,"external DAA bit exceeds candidate A1 bank");
            assert!(serializer_local<crate::header_hash::AUX_OFFSET,"serializer field exceeds its slot region");
            let left=DAA_RESULT_SLOT*work_tree_layout::WIDTH+daa_local;
            let right=header_slot*work_tree_layout::WIDTH+serializer_local;
            assert!(left<global_input_len&&right<global_input_len);
            let left_value=a1.witness[daa_wire];
            let right_value=serialized[header_slot][serializer_wire];
            assert!(coordinate_values.insert(left,left_value).is_none(),"duplicate mapped DAA coordinate");
            assert!(coordinate_values.insert(right,right_value).is_none(),"duplicate canonical serializer coordinate");
            let row=count.residual_rows+BANK_SLACK_ROWS+aliases.len();
            aliases.push(Term{row,gate:Gate{left,right,c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}});
        };

        for sample in 0..8{
            let header_slot=sample+1;
            for bit in 0..32{
                add_alias(a1.external[sample].nbits[bit],header_slot,
                    serializer.layout.fields.n_bits[bit]);
            }
        }
        for sample in 0..SAMPLE_COUNT{
            for bit in 0..64{
                let daa_wire=if sample==0{
                    a1.external[0].start_timestamp[bit]
                }else{
                    a1.external[sample-1].end_timestamp[bit]
                };
                if sample<8{
                    assert_eq!(a1.external[sample].start_timestamp[bit],daa_wire,
                        "adjacent DAA windows must share their timestamp wire");
                }
                add_alias(daa_wire,sample,serializer.layout.fields.timestamp[bit]);
            }
        }
        drop(add_alias);

        assert_eq!(aliases.len(),832);
        assert!(aliases.iter().enumerate().all(|(i,term)|
            term.row==count.residual_rows+BANK_SLACK_ROWS+i));
        assert!(aliases.iter().all(|term|
            term.gate.c0.is_zero()&&term.gate.c1==Fr::one()
                &&term.gate.c2==-Fr::one()&&term.gate.c3.is_zero()));
        assert!(aliases.iter().all(|term|
            term.gate.left<global_input_len&&term.gate.right<global_input_len));
        assert!(count.residual_rows+BANK_SLACK_ROWS+aliases.len()<=count.padded_rows,
            "field aliases exceed the existing DAA row domain");
        assert!(count.terms+BANK_SLACK_ROWS+aliases.len()<=daa_integer::MAX_MATERIAL_TERMS,
            "field aliases exceed the existing sparse term cap");

        fn equality_residual(gate:&Gate,left:Fr,right:Fr)->Fr{
            gate.c0+gate.c1*left+gate.c2*right+gate.c3*left*right
        }
        for term in &aliases{
            assert_eq!(equality_residual(&term.gate,
                coordinate_values[&term.gate.left],coordinate_values[&term.gate.right]),Fr::zero());
        }

        // Isolate a mutation on either side of one nBits equality.
        let nbits_alias=&aliases[0];
        let left=coordinate_values[&nbits_alias.gate.left];
        let right=coordinate_values[&nbits_alias.gate.right];
        let flipped_left=if left.is_zero(){Fr::one()}else{Fr::zero()};
        let flipped_right=if right.is_zero(){Fr::one()}else{Fr::zero()};
        assert_ne!(equality_residual(&nbits_alias.gate,flipped_left,right),Fr::zero());
        assert_ne!(equality_residual(&nbits_alias.gate,left,flipped_right),Fr::zero());

        // A one-sample timestamp shift must not satisfy the authenticated alias.
        let timestamp_sample=4;
        let timestamp_rows=8*32+timestamp_sample*64;
        let wrong_slot=timestamp_sample+1;
        let wrong_sample_residuals=(0..64).map(|bit|{
            let term=&aliases[timestamp_rows+bit];
            let wrong_right=wrong_slot*work_tree_layout::WIDTH+serializer_offset
                +serializer.layout.fields.timestamp[bit];
            equality_residual(&term.gate,coordinate_values[&term.gate.left],
                coordinate_values[&wrong_right])
        }).collect::<Vec<_>>();
        assert!(wrong_sample_residuals.iter().any(|value|!value.is_zero()),
            "wrong timestamp sample unexpectedly aliases the selected header");

        println!("A1 header aliases: rows={}, terms={}, input_log2={}, padded_DAA_rows={}, DAA_terms_with_bank_slack={}, remaining_rows={}, remaining_terms={}",
            aliases.len(),aliases.len(),global_input_len.trailing_zeros(),count.padded_rows,
            count.terms+BANK_SLACK_ROWS,
            count.padded_rows-count.residual_rows-BANK_SLACK_ROWS-aliases.len(),
            daa_integer::MAX_MATERIAL_TERMS-count.terms-BANK_SLACK_ROWS-aliases.len());

        // Reindex the materialized A1-A4 relation into the candidate banks,
        // then emit one immutable cross-slot edge list for the GKR roster.
        let a2=&composed.joined.joined.increment;
        let a3=&composed.joined.increment;
        let a4=&composed.increment;
        let original=composed.joined.joined.joined.circuit.as_ref().unwrap();
        let old_witness=&composed.joined.joined.joined.witness;
        assert_eq!(old_witness.len(),count.padded_input_bits);
        assert_eq!(original.input_len,count.padded_input_bits);
        assert_eq!(original.row_count,count.padded_rows);
        assert_eq!(original.terms.len(),count.terms);
        assert_eq!(a3.before,a2.after);
        assert_eq!(a4.before,a3.after);

        let a1_end=a2.before.live_bits;
        let a2_end=a2.after.live_bits;
        let a3_end=a3.after.live_bits;
        let padded=count.padded_input_bits;
        let spans=[(0,a1_end),(a1_end,a2_end),(a2_end,a3_end),(a3_end,padded)];
        let used=spans.map(|(start,end)|end-start);
        let mut wire_map=vec![usize::MAX;padded];
        for ((old_start,old_end),(_,bank_start,width)) in spans.into_iter().zip(PHASE_BANKS){
            assert!(old_end-old_start<=width,"DAA phase exceeds candidate bank");
            for old in old_start..old_end{
                let mapped=bank_start+(old-old_start);
                assert!(mapped<bank_start+width);
                assert_eq!(wire_map[old],usize::MAX,"candidate bank collision");
                wire_map[old]=mapped;
            }
        }
        assert!(wire_map.iter().all(|&wire|wire!=usize::MAX));
        assert_eq!(used.iter().sum::<usize>(),padded);
        assert_eq!(PHASE_BANKS.iter().zip(used).map(|((_,_,width),live)|width-live).sum::<usize>(),BANK_SLACK_ROWS);

        let child_nbits=composed.child_nbits.as_ref().expect("compiled child nBits wires");
        let child_alias_start=count.residual_rows+BANK_SLACK_ROWS+aliases.len();
        let a4_end=a4.after.live_bits;
        assert!(a4_end-a3_end<=PHASE_BANKS[3].2,"child DAA output exceeds the A4 candidate bank");
        assert!(padded-a3_end<=PHASE_BANKS[3].2,
            "A4 plus the child join and padding exceed the composed candidate bank");
        let child_aliases=child_nbits_alias_terms(child_nbits,&wire_map,old_witness,&serializer,
            &serialized[DAA_RESULT_SLOT],serializer_offset,DAA_RESULT_SLOT,child_alias_start,
            global_input_len,a4_end,count.live_bits,&mut coordinate_values);
        assert_eq!(child_aliases.len(),32);
        assert!(count.residual_rows+BANK_SLACK_ROWS+aliases.len()+child_aliases.len()<=count.padded_rows,
            "child nBits aliases exceed the DAA row domain");
        assert!(count.terms+BANK_SLACK_ROWS+aliases.len()+child_aliases.len()<=daa_integer::MAX_MATERIAL_TERMS,
            "child nBits aliases exceed the sparse term cap");

        let x0_alias_start=count.residual_rows+BANK_SLACK_ROWS+aliases.len()+child_aliases.len();
        let mut x0_aliases=Vec::<Term>::with_capacity(32);
        for (bit,&old_wire) in composed.joined.output.x0_bits.iter().enumerate(){
            assert!(old_wire>=a2_end&&old_wire<a3_end,
                "x0 bit must be allocated in the A3 prediction interval");
            let daa_local=wire_map[old_wire];
            let serializer_wire=serializer.layout.fields.height[bit];
            let left=DAA_RESULT_SLOT*work_tree_layout::WIDTH+daa_local;
            let right=work_tree_layout::WIDTH+serializer_offset+serializer_wire;
            assert!(daa_local>=PHASE_BANKS[2].1&&daa_local<PHASE_BANKS[2].1+PHASE_BANKS[2].2,
                "x0 input must be in the A3 candidate bank");
            assert!(left<global_input_len&&right<global_input_len&&left!=right);
            let left_value=old_witness[old_wire];
            let right_value=serialized[1][serializer_wire];
            assert_eq!(left_value,right_value,"x0 must equal the first quotient endpoint height");
            assert!(coordinate_values.insert(left,left_value).is_none(),"duplicate DAA x0 coordinate");
            assert!(coordinate_values.insert(right,right_value).is_none(),"duplicate serialized x0 height coordinate");
            let row=x0_alias_start+x0_aliases.len();
            x0_aliases.push(Term{row,gate:Gate{left,right,c0:Fr::zero(),c1:Fr::one(),
                c2:-Fr::one(),c3:Fr::zero()}});
        }
        assert_eq!(x0_aliases.len(),32);
        assert!(count.residual_rows+BANK_SLACK_ROWS+aliases.len()+child_aliases.len()+x0_aliases.len()
            <=count.padded_rows,"x0 height aliases exceed the DAA row domain");
        assert!(count.terms+BANK_SLACK_ROWS+aliases.len()+child_aliases.len()+x0_aliases.len()
            <=daa_integer::MAX_MATERIAL_TERMS,"x0 height aliases exceed the sparse term cap");

        let mut sparse_witness=BTreeMap::<usize,Fr>::new();
        let mut put_value=|coordinate:usize,value:Fr|{
            if !value.is_zero(){
                assert!(sparse_witness.insert(coordinate,value).is_none(),"duplicate nonzero witness coordinate");
            }
        };
        for (old,&mapped) in wire_map.iter().enumerate(){
            put_value(DAA_RESULT_SLOT*work_tree_layout::WIDTH+mapped,old_witness[old]);
        }
        for (slot,assignment) in serialized.iter().enumerate(){
            for (wire,&value) in assignment.iter().enumerate(){
                if !value.is_zero(){put_value(slot*work_tree_layout::WIDTH+serializer_offset+wire,value);}
            }
        }
        drop(put_value);
        for (&coordinate,&value) in &coordinate_values{
            assert_eq!(sparse_witness.get(&coordinate).copied().unwrap_or_else(Fr::zero),value,
                "mapped sparse witness disagrees with a public field alias");
        }

        let mut edges=Vec::<crate::sparse_stream_roster::EdgeTerm>::with_capacity(
            original.terms.len()+BANK_SLACK_ROWS+aliases.len()+child_aliases.len()+x0_aliases.len());
        for term in &original.terms{
            let left_active=!term.gate.c1.is_zero()||!term.gate.c3.is_zero();
            let right_active=!term.gate.c2.is_zero()||!term.gate.c3.is_zero();
            let mapped_left=if left_active{
                DAA_RESULT_SLOT*work_tree_layout::WIDTH+wire_map[term.gate.left]
            }else if right_active{
                DAA_RESULT_SLOT*work_tree_layout::WIDTH+wire_map[term.gate.right]
            }else{
                DAA_RESULT_SLOT*work_tree_layout::WIDTH+PHASE_BANKS[0].1
            };
            let mapped_right=if right_active{
                DAA_RESULT_SLOT*work_tree_layout::WIDTH+wire_map[term.gate.right]
            }else{mapped_left};
            let gate=Gate{left:mapped_left,right:mapped_right,c0:term.gate.c0,c1:term.gate.c1,
                c2:term.gate.c2,c3:term.gate.c3};
            edges.push(crate::sparse_stream_roster::EdgeTerm{source_slot:DAA_RESULT_SLOT,
                family_row:term.row,term:Term{row:term.row,gate}});
        }
        for ((_,bank_start,width),live) in PHASE_BANKS.into_iter().zip(used){
            for wire in bank_start+live..bank_start+width{
                let endpoint=DAA_RESULT_SLOT*work_tree_layout::WIDTH+wire;
                edges.push(crate::sparse_stream_roster::EdgeTerm{source_slot:DAA_RESULT_SLOT,
                    family_row:count.residual_rows+(edges.len()-original.terms.len()),
                    term:Term{row:count.residual_rows+(edges.len()-original.terms.len()),
                        gate:Gate{left:endpoint,right:endpoint,c0:Fr::zero(),c1:Fr::one(),
                            c2:Fr::zero(),c3:Fr::zero()}}});
            }
        }
        for term in &aliases{
            edges.push(crate::sparse_stream_roster::EdgeTerm{source_slot:DAA_RESULT_SLOT,
                family_row:term.row,term:term.clone()});
        }
        for term in &child_aliases{
            edges.push(crate::sparse_stream_roster::EdgeTerm{source_slot:DAA_RESULT_SLOT,
                family_row:term.row,term:term.clone()});
        }
        for term in &x0_aliases{
            edges.push(crate::sparse_stream_roster::EdgeTerm{source_slot:DAA_RESULT_SLOT,
                family_row:term.row,term:term.clone()});
        }
        assert_eq!(edges.len(),original.terms.len()+BANK_SLACK_ROWS+aliases.len()+child_aliases.len()+x0_aliases.len());
        assert!(count.residual_rows+BANK_SLACK_ROWS+aliases.len()+child_aliases.len()+x0_aliases.len()<=count.padded_rows);
        assert!(edges.iter().all(|edge|edge.family_row<1<<17&&edge.term.row==edge.family_row
            &&edge.source_slot==DAA_RESULT_SLOT&&edge.term.gate.left<global_input_len
            &&edge.term.gate.right<global_input_len));

        let value_at=|coordinate:usize,witness:&BTreeMap<usize,Fr>|{
            witness.get(&coordinate).copied().unwrap_or_else(Fr::zero)
        };
        let edge_residuals=|witness:&BTreeMap<usize,Fr>|{
            let mut rows=vec![Fr::zero();count.padded_rows];
            for edge in &edges{
                rows[edge.term.row]+=edge.term.gate.c0
                    +edge.term.gate.c1*value_at(edge.term.gate.left,witness)
                    +edge.term.gate.c2*value_at(edge.term.gate.right,witness)
                    +edge.term.gate.c3*value_at(edge.term.gate.left,witness)
                        *value_at(edge.term.gate.right,witness);
            }
            rows
        };
        let mut expected_rows=circuit_residuals(original,old_witness);
        assert!(expected_rows.iter().all(Zero::is_zero),"materialized DAA witness has a nonzero row");
        let emitted_rows=edge_residuals(&sparse_witness);
        expected_rows.resize(count.padded_rows,Fr::zero());
        assert_eq!(emitted_rows,expected_rows,"edge reindexing changed the materialized residual relation");

        // Carry isolated nonzero mutations through the original phase wires,
        // candidate-bank map, and canonical edge relation. A zero-only check
        // could miss a bad map that happens to select another zero-valued wire.
        for old_wire in [0,a1_end,a2_end,a3_end,count.live_bits]{
            assert!(old_wire<padded);
            let mut changed_old=old_witness.clone();
            changed_old[old_wire]=Fr::from(2u64);
            let expected=circuit_residuals(original,&changed_old);
            assert!(expected[..count.residual_rows].iter().any(|value|!value.is_zero()),
                "mutated source wire {old_wire} did not activate an original residual");
            let mut changed_sparse=sparse_witness.clone();
            changed_sparse.insert(DAA_RESULT_SLOT*work_tree_layout::WIDTH+wire_map[old_wire],Fr::from(2u64));
            let actual=edge_residuals(&changed_sparse);
            assert_eq!(actual[..count.residual_rows],expected[..count.residual_rows],
                "canonical edge relation changed original rows for source wire {old_wire}");
            assert!(actual[count.residual_rows..count.residual_rows+BANK_SLACK_ROWS]
                .iter().all(Zero::is_zero),"live-wire mutation reached bank-slack rows");
        }
        let first_external_wire=a1.external[0].nbits[0];
        assert_eq!(first_external_wire,0);
        let first_alias=&aliases[0];
        let changed_alias_left=value_at(first_alias.gate.left,&sparse_witness);
        let changed_alias_right=value_at(first_alias.gate.right,&sparse_witness);
        let alias_mutated_rows={
            let mut changed=sparse_witness.clone();
            changed.insert(first_alias.gate.left,Fr::from(2u64));
            edge_residuals(&changed)
        };
        let expected_alias=equality_residual(&first_alias.gate,Fr::from(2u64),changed_alias_right);
        assert_ne!(expected_alias,Fr::zero());
        assert_eq!(alias_mutated_rows[first_alias.row],expected_alias,
            "cross-slot edge alias row differs under an isolated DAA-side mutation");
        assert_eq!(changed_alias_left,sparse_witness.get(&first_alias.gate.left).copied().unwrap_or_else(Fr::zero));

        // The optimized endpoint rosters must be the exact multisets obtained
        // by independently filtering the immutable edge list.
        let mut left_indices=vec![Vec::<usize>::new();slots];
        let mut right_indices=vec![Vec::<usize>::new();slots];
        for (index,edge) in edges.iter().enumerate(){
            left_indices[edge.term.gate.left/work_tree_layout::WIDTH].push(index);
            right_indices[edge.term.gate.right/work_tree_layout::WIDTH].push(index);
        }
        for slot in 0..slots{
            let expected_left=edges.iter().enumerate().filter_map(|(index,edge)|
                (edge.term.gate.left/work_tree_layout::WIDTH==slot).then_some(index)).collect::<Vec<_>>();
            let expected_right=edges.iter().enumerate().filter_map(|(index,edge)|
                (edge.term.gate.right/work_tree_layout::WIDTH==slot).then_some(index)).collect::<Vec<_>>();
            assert_eq!(left_indices[slot],expected_left,"left endpoint roster differs at slot {slot}");
            assert_eq!(right_indices[slot],expected_right,"right endpoint roster differs at slot {slot}");
        }
        assert_eq!(left_indices.iter().map(Vec::len).sum::<usize>(),edges.len());
        assert_eq!(right_indices.iter().map(Vec::len).sum::<usize>(),edges.len());

        // Compare coefficients emitted through the left endpoint roster with
        // a scalar reference sum over the exact canonicalized edge relation.
        let r=(0..21).map(|bit|Fr::from(bit as u64+2)).collect::<Vec<_>>();
        let u=(0..24).map(|bit|Fr::from((bit as u64%7)+3)).collect::<Vec<_>>();
        let v=(0..24).map(|bit|Fr::from((bit as u64%11)+4)).collect::<Vec<_>>();
        let mut via_endpoints=[Fr::zero();4];
        for slot in 0..slots{
            for &index in &left_indices[slot]{
                let edge=&edges[index];
                let row=(edge.source_slot<<17)|edge.family_row;
                let weight=scalar_eq_weight(&r,row)*scalar_eq_weight(&u,edge.term.gate.left)
                    *scalar_eq_weight(&v,edge.term.gate.right);
                via_endpoints[0]+=weight*edge.term.gate.c0;
                via_endpoints[1]+=weight*edge.term.gate.c1;
                via_endpoints[2]+=weight*edge.term.gate.c2;
                via_endpoints[3]+=weight*edge.term.gate.c3;
            }
        }
        let edge_wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|->Result<[Fr;4],String>{
            if r.len()!=21||u.len()!=24||v.len()!=24{return Err("DAA edge wiring point dimension".into());}
            let mut out=[Fr::zero();4];
            for edge in &edges{
                let row=(edge.source_slot<<17)|edge.family_row;
                let weight=crate::work_tree_wiring::eq_index(r,row)
                    *crate::work_tree_wiring::eq_index(u,edge.term.gate.left)
                    *crate::work_tree_wiring::eq_index(v,edge.term.gate.right);
                out[0]+=weight*edge.term.gate.c0;
                out[1]+=weight*edge.term.gate.c1;
                out[2]+=weight*edge.term.gate.c2;
                out[3]+=weight*edge.term.gate.c3;
            }
            Ok(out)
        };
        let direct=edge_wiring(&r,&u,&v).unwrap();
        assert_eq!(via_endpoints,direct,"endpoint coefficient roster differs from direct relation sum");

        // Bounded repeated-window differential. q=9 is the first result slot
        // with its nine sample headers at slots 0..8. Values are arithmetic
        // fixtures, not a historical height schedule or activation proof.
        let kernel_end=original.terms.len()+BANK_SLACK_ROWS;
        assert_eq!(edges.len(),kernel_end+aliases.len()+child_aliases.len()+x0_aliases.len());
        let repeated_edges=edges.clone();
        let repeated_explicit=|r:&[Fr],u:&[Fr],v:&[Fr]|{
            let mut out=[Fr::zero();4];
            for parent in DAA_RESULT_SLOT..16{
                for edge in &repeated_edges{
                    let source_right=edge.term.gate.right/work_tree_layout::WIDTH;
                    assert!(source_right<=DAA_RESULT_SLOT);
                    let offset=DAA_RESULT_SLOT-source_right;
                    if parent<offset{continue;}
                    let row=(parent<<17)|edge.family_row;
                    let left=parent*work_tree_layout::WIDTH
                        +edge.term.gate.left%work_tree_layout::WIDTH;
                    let right=(parent-offset)*work_tree_layout::WIDTH
                        +edge.term.gate.right%work_tree_layout::WIDTH;
                    let weight=scalar_eq_weight(r,row)*scalar_eq_weight(u,left)
                        *scalar_eq_weight(v,right);
                    out[0]+=weight*edge.term.gate.c0;
                    out[1]+=weight*edge.term.gate.c1;
                    out[2]+=weight*edge.term.gate.c2;
                    out[3]+=weight*edge.term.gate.c3;
                }
            }
            out
        };
        let repeated_analytic=|r:&[Fr],u:&[Fr],v:&[Fr]|->Result<[Fr;4],String>{
            if r.len()!=21||u.len()!=24||v.len()!=24{
                return Err("repeated DAA wiring point dimension".into());
            }
            let (rl,rh)=r.split_at(17);
            let (ul,uh)=u.split_at(20);
            let (vl,vh)=v.split_at(20);
            let mut out=[Fr::zero();4];
            for edge in &repeated_edges[..kernel_end]{
                let weight=scalar_eq_weight(rl,edge.family_row)
                    *scalar_eq_weight(ul,edge.term.gate.left%work_tree_layout::WIDTH)
                    *scalar_eq_weight(vl,edge.term.gate.right%work_tree_layout::WIDTH);
                out[0]+=weight*edge.term.gate.c0;
                out[1]+=weight*edge.term.gate.c1;
                out[2]+=weight*edge.term.gate.c2;
                out[3]+=weight*edge.term.gate.c3;
            }
            let local_factor=crate::wiring::evaluate_shift(
                rh,uh,vh,0,DAA_RESULT_SLOT as u64,16,0,crate::wiring::RightIndex::SameRow)?;
            for coefficient in &mut out{*coefficient*=local_factor;}

            // Imported fields lie at q-offset. Swap the input selector order
            // so evaluate_shift's (i-offset, i) pair is (right, left).
            let mut imports=[[Fr::zero();4];DAA_RESULT_SLOT+1];
            for edge in &repeated_edges[kernel_end..]{
                let source_right=edge.term.gate.right/work_tree_layout::WIDTH;
                assert!(source_right<=DAA_RESULT_SLOT);
                let offset=DAA_RESULT_SLOT-source_right;
                let weight=scalar_eq_weight(rl,edge.family_row)
                    *scalar_eq_weight(ul,edge.term.gate.left%work_tree_layout::WIDTH)
                    *scalar_eq_weight(vl,edge.term.gate.right%work_tree_layout::WIDTH);
                imports[offset][0]+=weight*edge.term.gate.c0;
                imports[offset][1]+=weight*edge.term.gate.c1;
                imports[offset][2]+=weight*edge.term.gate.c2;
                imports[offset][3]+=weight*edge.term.gate.c3;
            }
            for offset in 0..=DAA_RESULT_SLOT{
                let factor=crate::wiring::evaluate_shift(
                    rh,vh,uh,offset as u64,DAA_RESULT_SLOT as u64,16,0,crate::wiring::RightIndex::SameRow)?;
                for coefficient in 0..4{out[coefficient]+=imports[offset][coefficient]*factor;}
            }
            Ok(out)
        };
        for seed in [2u64,17,101]{
            let rr=(0..21).map(|bit|Fr::from(seed+2*bit as u64+3)).collect::<Vec<_>>();
            let uu=(0..24).map(|bit|Fr::from(seed+3*bit as u64+17)).collect::<Vec<_>>();
            let vv=(0..24).map(|bit|Fr::from(seed+5*bit as u64+43)).collect::<Vec<_>>();
            assert_eq!(repeated_explicit(&rr,&uu,&vv),
                repeated_analytic(&rr,&uu,&vv).unwrap(),
                "analytic repeated DAA wiring differs from explicit expansion at seed {seed}");
        }
        let x0_edge=&repeated_edges[kernel_end+aliases.len()+child_aliases.len()];
        let onehot=|bits:usize,index:usize| (0..bits)
            .map(|bit|Fr::from(((index>>bit)&1) as u64)).collect::<Vec<_>>();
        let isolated=repeated_analytic(
            &onehot(21,(DAA_RESULT_SLOT<<17)|x0_edge.family_row),
            &onehot(24,DAA_RESULT_SLOT*work_tree_layout::WIDTH+x0_edge.term.gate.left%work_tree_layout::WIDTH),
            &onehot(24,work_tree_layout::WIDTH+x0_edge.term.gate.right%work_tree_layout::WIDTH))
            .unwrap();
        assert_eq!(isolated,[Fr::zero(),Fr::one(),-Fr::one(),Fr::zero()],
            "height/x0 alias must isolate at the first full sample window");
        drop(repeated_edges);

        // A single source-slot mutation must change the output selector weight.
        let edge=&edges[0];
        let correct_row=(edge.source_slot<<17)|edge.family_row;
        let wrong_row=((edge.source_slot-1)<<17)|edge.family_row;
        assert_ne!(crate::work_tree_wiring::eq_index(&r,correct_row),
            crate::work_tree_wiring::eq_index(&r,wrong_row),"source-slot mutation was not distinguished");
        let alias=&edges[original.terms.len()+BANK_SLACK_ROWS];
        let left=value_at(alias.term.gate.left,&sparse_witness);
        let right=value_at(alias.term.gate.right,&sparse_witness);
        assert_eq!(equality_residual(&alias.term.gate,left,right),Fr::zero());
        assert_ne!(equality_residual(&alias.term.gate,left+Fr::one(),right),Fr::zero(),
            "one-bit DAA-side mutation was not detected by its edge row");
        let child_alias=&edges[original.terms.len()+BANK_SLACK_ROWS+aliases.len()];
        assert_eq!(child_alias.source_slot,DAA_RESULT_SLOT);
        let child_left=value_at(child_alias.term.gate.left,&sparse_witness);
        let child_right=value_at(child_alias.term.gate.right,&sparse_witness);
        assert_eq!(equality_residual(&child_alias.term.gate,child_left,child_right),Fr::zero());
        let child_left_mutation={
            let mut changed=sparse_witness.clone();
            changed.insert(child_alias.term.gate.left,child_left+Fr::one());
            edge_residuals(&changed)
        };
        assert_ne!(child_left_mutation[child_alias.family_row],Fr::zero(),
            "child nBits DAA-side mutation was not detected by its edge row");
        let child_right_mutation={
            let mut changed=sparse_witness.clone();
            changed.insert(child_alias.term.gate.right,child_right+Fr::one());
            edge_residuals(&changed)
        };
        assert_ne!(child_right_mutation[child_alias.family_row],Fr::zero(),
            "child nBits serializer-side mutation was not detected by its edge row");

        let x0_alias=&edges[kernel_end+aliases.len()+child_aliases.len()];
        assert_eq!(x0_alias.source_slot,DAA_RESULT_SLOT);
        let x0_left=value_at(x0_alias.term.gate.left,&sparse_witness);
        let x0_right=value_at(x0_alias.term.gate.right,&sparse_witness);
        assert_eq!(equality_residual(&x0_alias.term.gate,x0_left,x0_right),Fr::zero());
        let x0_left_mutation={
            let mut changed=sparse_witness.clone();
            changed.insert(x0_alias.term.gate.left,x0_left+Fr::one());
            edge_residuals(&changed)
        };
        assert_ne!(x0_left_mutation[x0_alias.family_row],Fr::zero(),
            "x0 DAA-side mutation was not detected by its committed edge row");
        let x0_right_mutation={
            let mut changed=sparse_witness.clone();
            changed.insert(x0_alias.term.gate.right,x0_right+Fr::one());
            edge_residuals(&changed)
        };
        assert_ne!(x0_right_mutation[x0_alias.family_row],Fr::zero(),
            "serialized height mutation was not detected by its committed edge row");

        // Add the bounded field-to-byte projection as a second relation family
        // in the already committed 21-bit row domain. The repeated-window
        // differential is complete; preserve only the DAA prefix count when
        // transferring those validated edges into the combined roster.
        let projection_row_start=count.residual_rows+BANK_SLACK_ROWS+aliases.len()
            +child_aliases.len()+x0_aliases.len();
        let projection_row_end=projection_row_start+projection.residual_rows;
        assert!(projection_row_end<=count.padded_rows,
            "serializer field projection exceeds remaining local DAA rows");
        let projection_aux_start=serializer.stats.used_input_bits;
        let projection_max_wire=projection.circuit.terms.iter()
            .flat_map(|term|[term.gate.left,term.gate.right]).max().unwrap();
        let projection_aux_end=projection_max_wire+1;
        assert!(projection_aux_end<=serializer.circuit.input_len);
        assert!(projection_aux_start<projection_aux_end);
        let projection_aux_count=projection_aux_end-projection_aux_start;
        assert_eq!(PROJECTION_AUX_START,PHASE_BANKS[1].1+PHASE_BANKS[1].2,
            "projection auxiliary bank must follow DAA A2");
        assert_eq!(PROJECTION_AUX_END,PHASE_BANKS[2].1,
            "projection auxiliary bank must end before DAA A3");
        assert!(PROJECTION_AUX_START>=655_628
            && PROJECTION_AUX_START+projection_aux_count<=720_896,
            "projection auxiliaries must remain in the shared header-allocation gap");
        assert!(PROJECTION_AUX_START+projection_aux_count<=PROJECTION_AUX_END,
            "projection auxiliaries exceed their reserved local bank");
        assert_eq!(projection_aux_count,384,
            "projection auxiliary allocation changed; re-review the global map");
        let projection_terms=serialized.len()*projection.circuit.terms.len();
        let baseline_edge_count=edges.len();
        assert!(baseline_edge_count+projection_terms<=daa_integer::MAX_MATERIAL_TERMS,
            "projected DAA relation exceeds the sparse term cap");

        let mut proof_edges=Vec::<crate::sparse_stream_roster::EdgeTerm>::with_capacity(
            baseline_edge_count+projection_terms);
        proof_edges.extend(edges);
        let map_projection_wire=|slot:usize,wire:usize|->usize{
            assert!(wire<serializer.circuit.input_len,"projection wire exceeds serializer input");
            if wire>=projection_aux_start{
                assert!(wire<projection_aux_end,"projection references an unallocated padding wire");
                slot*work_tree_layout::WIDTH+PROJECTION_AUX_START+(wire-projection_aux_start)
            }else{
                slot*work_tree_layout::WIDTH+serializer_offset+wire
            }
        };
        for (slot,assignment) in serialized.iter().enumerate(){
            let projected=projection.assign(assignment).unwrap();
            for wire in projection_aux_start..projection_aux_end{
                let coordinate=slot*work_tree_layout::WIDTH+PROJECTION_AUX_START
                    +(wire-projection_aux_start);
                assert!(!sparse_witness.contains_key(&coordinate),
                    "projection auxiliary overlaps an existing committed wire");
                let value=projected[wire];
                if !value.is_zero(){sparse_witness.insert(coordinate,value);}
            }
            for original in &projection.circuit.terms{
                let row=projection_row_start+original.row;
                let gate=Gate{
                    left:map_projection_wire(slot,original.gate.left),
                    right:map_projection_wire(slot,original.gate.right),
                    c0:original.gate.c0,c1:original.gate.c1,
                    c2:original.gate.c2,c3:original.gate.c3};
                proof_edges.push(crate::sparse_stream_roster::EdgeTerm{
                    source_slot:slot,family_row:row,term:Term{row,gate}});
            }
        }
        assert_eq!(proof_edges.len(),baseline_edge_count+projection_terms);
        assert!(proof_edges.iter().all(|edge|edge.source_slot<slots
            &&edge.family_row<1<<17&&edge.term.row==edge.family_row
            &&edge.term.gate.left<global_input_len&&edge.term.gate.right<global_input_len),
            "combined relation contains an edge outside its slot/row/input allocation");

        let edge_source=MatureDaaProofEdgeSource{
            original,wire_map:&wire_map,used,result_slot:DAA_RESULT_SLOT,daa_row_start:count.residual_rows,
            bank_slack_rows:BANK_SLACK_ROWS,aliases:&aliases,child_aliases:&child_aliases,
            x0_aliases:&x0_aliases,projection:&projection.circuit,
            projection_residual_rows:projection.residual_rows,projection_row_start,
            projection_aux_start,projection_aux_end,projection_aux_bank_start:PROJECTION_AUX_START,
            serializer_offset,serializer_input_len:serializer.circuit.input_len,
            projection_slots:serialized.len(),
        };
        let mut streamed_index=0usize;
        edge_source.emit_all(&mut |emitted|{
            let expected=proof_edges.get(streamed_index)
                .ok_or("mature DAA source emitted more terms than its resident oracle")?;
            if emitted.source_slot!=expected.source_slot||emitted.family_row!=expected.family_row
                ||emitted.term!=expected.term{
                return Err(format!("mature DAA streamed edge differs from resident oracle at {streamed_index}"));
            }
            streamed_index+=1;
            Ok(())
        }).unwrap();
        assert_eq!(streamed_index,proof_edges.len(),
            "mature DAA source omitted terms from its resident oracle");

        if wiring_only{
            diagnose_retained_daa_factorization(&edge_source,&proof_edges);
            return;
        }

        // Bind every header used by DAA to its native BLAKE2 digest under the
        // same packed commitment. Keep only packed core bytes per slot here;
        // the full hash witness and temporary circuit are released each loop.
        const HASH_SLOT_COUNT:usize=SAMPLE_COUNT+1;
        let mut hash_raws=headers.iter().map(|header|header.encode().unwrap()).collect::<Vec<_>>();
        let child_raw=child_header.encode().unwrap();
        assert_eq!(child_raw.len(),child_bytes.len(),"fixed-width nBits substitution must preserve encoded length");
        hash_raws.push(child_raw);
        assert_eq!(hash_raws.len(),HASH_SLOT_COUNT);
        let mut hash_heights=headers.iter().map(|header|header.height).collect::<Vec<_>>();
        hash_heights.push(child_header.height);
        assert_eq!(hash_heights.len(),HASH_SLOT_COUNT);
        assert_eq!(hash_raws[0].len(),278,"slot 0 fixture serialization length changed");
        assert!(hash_raws[1..].iter().all(|raw|raw.len()==279),"sample/child serialization length changed");
        let mut hash_fields=fields.clone();hash_fields.push(child_fields.clone());
        let expected_header_digests=hash_raws.iter().map(|raw|ergo_header_core::blake2b256(raw))
            .collect::<Vec<_>>();

        let mut hash_core:Option<crate::sparse::Circuit>=None;
        let mut hash_core_compression_layout:Option<crate::circuit::CompressionLayout>=None;
        let mut hash_boundary_rows:Option<crate::header_hash::BoundaryRows>=None;
        let mut hash_boundary_base:Option<crate::sparse::Circuit>=None;
        let mut hash_core_overlays=Vec::<Vec<u8>>::with_capacity(HASH_SLOT_COUNT);
        let mut hash_aux_overlays=Vec::<[u8;12]>::with_capacity(HASH_SLOT_COUNT);
        let mut hash_boundary_term_digests=Vec::<String>::with_capacity(HASH_SLOT_COUNT);
        let mut removed_hash_padding=0usize;

        for slot in 0..HASH_SLOT_COUNT{
            let expected_digest=expected_header_digests[slot];
            let mut joined=crate::header_hash::build(Some(&hash_fields[slot]),expected_digest).unwrap();
            let mut header_hash_input=joined.input.take().unwrap();
            assert_eq!(header_hash_input.len(),work_tree_layout::WIDTH);
            assert_eq!(&header_hash_input[serializer_offset..crate::header_hash::AUX_OFFSET],serialized[slot].as_slice());

            if slot==0{
                hash_core=Some(joined.core.clone());
                hash_core_compression_layout=Some(joined.compression_layout.clone());
                hash_boundary_rows=Some(joined.boundary_rows.clone());
            }else{
                assert_eq!(&joined.core,hash_core.as_ref().unwrap(),"BLAKE compression relation changed between slots");
                assert_eq!(joined.compression_layout,hash_core_compression_layout.as_ref().unwrap().clone());
                assert_eq!(joined.boundary_rows,hash_boundary_rows.as_ref().unwrap().clone());
            }

            let encoded_bytes=serializer.layout.bytes.iter().map(|wires|wires.iter().enumerate()
                .fold(0u8,|byte,(bit,wire)|if serialized[slot][*wire].is_one(){byte|(1u8<<bit)}else{byte}))
                .collect::<Vec<_>>();
            let encoded_length=serializer.layout.length.iter().enumerate()
                .map(|(bit,wire)|if serialized[slot][*wire].is_one(){1usize<<bit}else{0}).sum::<usize>();
            assert_eq!(encoded_length,hash_raws[slot].len(),
                "public serialized length must come from the independently encoded native header");
            assert_eq!(&encoded_bytes[..encoded_length],hash_raws[slot].as_slice(),
                "native header digest must cover the exact committed serializer bytes");

            for wire in PROJECTION_AUX_START..PROJECTION_AUX_END{
                let coordinate=slot*work_tree_layout::WIDTH+wire;
                header_hash_input[wire]=sparse_witness.get(&coordinate).copied().unwrap_or_else(Fr::zero);
            }
            let removed=joined.boundary.terms.iter()
                .filter(|term|joined.boundary_rows.global_padding.contains(&term.row)).count();
            if slot==0{removed_hash_padding=removed;assert_eq!(removed_hash_padding,393_204,"hash padding anchor inventory changed");}
            else{assert_eq!(removed,removed_hash_padding,"hash padding inventory changed between slots");}
            let (canonical_length_terms,canonical_length_rows)=crate::header_hash::canonical_length_padding_rows(
                &joined.serializer.layout,hash_raws[slot].len(),joined.boundary_rows.global_padding.end).unwrap();
            let canonical_length_term_count=canonical_length_terms.len();
            assert_eq!(canonical_length_rows.len(),4_123,"public length/tail-padding row inventory changed");
            let mut hash_boundary=joined.boundary;
            let mut live_terms=Vec::with_capacity(30_890-canonical_length_term_count);
            for term in hash_boundary.terms.drain(..){
                if !joined.boundary_rows.global_padding.contains(&term.row){live_terms.push(term);}
            }
            hash_boundary.terms=live_terms;
            assert!(hash_boundary.terms.iter().all(|term|!canonical_length_rows.contains(&term.row)),
                "canonical length rows overlap a live hash-boundary row");
            hash_boundary.terms.extend(canonical_length_terms);
            assert_eq!(hash_boundary.input_len,work_tree_layout::WIDTH);
            assert_eq!(hash_boundary.row_count,1<<19);
            assert_eq!(hash_boundary.terms.len(),30_890,
                "canonical BLAKE boundary changed outside its omitted global-padding family");
            assert!(circuit_residuals(&hash_boundary,&header_hash_input).iter().all(Zero::is_zero),
                "BLAKE message/chaining/digest and exact public-length boundary must hold for every DAA slot");
            hash_boundary_term_digests.push(work_tree_layout::hash_terms(&hash_boundary.terms));

            let mut mutated_serializer=serialized[slot].clone();
            let unrelated_byte_wire=serializer.layout.bytes[0][0];
            mutated_serializer[unrelated_byte_wire]=if mutated_serializer[unrelated_byte_wire].is_zero(){Fr::one()}else{Fr::zero()};
            let mutated_projection=projection.assign(&mutated_serializer).unwrap();
            assert!(circuit_residuals(&projection.circuit,&mutated_projection).iter().all(Zero::is_zero),
                "selected-field projection must not depend on an unrelated version byte");
            let mut mutated_hash_input=header_hash_input.clone();
            mutated_hash_input[serializer_offset+unrelated_byte_wire]=mutated_serializer[unrelated_byte_wire];
            let mutated_hash_rows=circuit_residuals(&hash_boundary,&mutated_hash_input);
            let message_aliases=joined.boundary_rows.message_aliases.clone();
            assert!(mutated_hash_rows[message_aliases.clone()].iter().any(|value|!value.is_zero()),
                "slot {slot} preimage mutation with fixed digest must fail its BLAKE message alias");
            assert!(mutated_hash_rows.iter().enumerate().all(|(row,value)|message_aliases.contains(&row)||value.is_zero()),
                "slot {slot} unrelated-byte mutation must fail only at its BLAKE message alias");

            let (wrong_length_terms,wrong_length_rows)=crate::header_hash::canonical_length_padding_rows(
                &joined.serializer.layout,hash_raws[slot].len()+1,joined.boundary_rows.global_padding.end).unwrap();
            let wrong_length_relation=crate::sparse::Circuit { input_len:hash_boundary.input_len,
                row_count:hash_boundary.row_count,terms:wrong_length_terms };
            let wrong_length_residuals=circuit_residuals(&wrong_length_relation,&header_hash_input);
            assert_eq!(wrong_length_residuals.iter().enumerate()
                .filter_map(|(row,value)|(!value.is_zero()).then_some(row)).collect::<Vec<_>>(),
                vec![wrong_length_rows.start+10],"slot {slot} wrong public length must fail only its equality row");

            let tail_byte=encoded_length;
            assert!(tail_byte<514,"fixture needs a byte inside the BLAKE final-block padding suffix");
            let tail_serializer_wire=joined.serializer.layout.bytes[tail_byte][0];
            let tail_message_wire=(tail_byte/128)*crate::header_hash::CORE_WIDTH
                +joined.compression_layout.message[(tail_byte%128)/8][(tail_byte%8)*8];
            let mut tail_mutant=header_hash_input.clone();
            assert!(tail_mutant[serializer_offset+tail_serializer_wire].is_zero());
            tail_mutant[serializer_offset+tail_serializer_wire]=Fr::one();
            tail_mutant[tail_message_wire]=Fr::one();
            let tail_residuals=circuit_residuals(&hash_boundary,&tail_mutant);
            assert!(tail_residuals[canonical_length_rows.clone()].iter().any(|value|!value.is_zero()),
                "slot {slot} nonzero suffix must fail its exact tail-padding family");
            assert!(tail_residuals[message_aliases.clone()].iter().all(Zero::is_zero),
                "slot {slot} suffix mutant must retain the serializer-to-message alias");
            assert!(tail_residuals.iter().enumerate()
                .all(|(row,value)|canonical_length_rows.contains(&row)||value.is_zero()),
                "slot {slot} suffix-byte mutant must fail only the exact tail-padding family");
            if slot==0{
                let mut omitted_tail=hash_boundary.clone();
                omitted_tail.terms.retain(|term|!canonical_length_rows.contains(&term.row));
                assert!(circuit_residuals(&omitted_tail,&tail_mutant).iter().all(Zero::is_zero),
                    "omitting exact tail padding must admit the isolated nonzero-suffix mutant");

                let mut base_terms=Vec::with_capacity(hash_boundary.terms.len()-canonical_length_term_count);
                let mut digest_constants=vec![false;joined.boundary_rows.digest.len()];
                for mut term in hash_boundary.terms.drain(..){
                    if canonical_length_rows.contains(&term.row){continue;}
                    if joined.boundary_rows.digest.contains(&term.row)
                        &&term.gate.c1.is_zero()&&term.gate.c2.is_zero()&&term.gate.c3.is_zero(){
                        let bit=term.row-joined.boundary_rows.digest.start;
                        term.gate.c0=Fr::zero();digest_constants[bit]=true;
                    }
                    base_terms.push(term);
                }
                assert!(digest_constants.iter().all(|seen|*seen),"digest rows must each contain one replaceable constant");
                hash_boundary.terms=base_terms;
                assert_eq!(hash_boundary.terms.len(),26_757,"shared hash boundary template term count changed");
                hash_boundary_base=Some(hash_boundary);
            }

            let mut packed_core=vec![0u8;crate::header_hash::SERIALIZER_OFFSET/8];
            for (wire,value) in header_hash_input[..crate::header_hash::SERIALIZER_OFFSET].iter().copied().enumerate(){
                assert!(value.is_zero()||value.is_one(),"BLAKE core witness must be Boolean");
                if value.is_one(){packed_core[wire/8]|=1<<(wire%8);}
                let coordinate=slot*work_tree_layout::WIDTH+wire;
                if let Some(previous)=sparse_witness.get(&coordinate){
                    assert_eq!(*previous,value,"BLAKE core witness overlaps an existing committed wire");
                }
            }
            let packed_aux=std::array::from_fn(|index|{
                let value=header_hash_input[crate::header_hash::AUX_OFFSET+index];
                assert!(value.is_zero()||value.is_one(),"BLAKE auxiliary witness must be Boolean");
                let coordinate=slot*work_tree_layout::WIDTH+crate::header_hash::AUX_OFFSET+index;
                if let Some(previous)=sparse_witness.get(&coordinate){
                    assert_eq!(*previous,value,"BLAKE auxiliary witness overlaps an existing committed wire");
                }
                value.is_one() as u8
            });
            hash_core_overlays.push(packed_core);
            hash_aux_overlays.push(packed_aux);
            drop(mutated_hash_input);
            drop(header_hash_input);
        }

        let hash_core=hash_core.unwrap();
        let hash_core_compression_layout=hash_core_compression_layout.unwrap();
        let hash_boundary_rows=hash_boundary_rows.unwrap();
        let hash_boundary_base=hash_boundary_base.unwrap();
        let build_hash_boundary=|slot:usize|->(crate::sparse::Circuit,std::ops::Range<usize>){
            assert!(slot<HASH_SLOT_COUNT);
            let mut boundary=hash_boundary_base.clone();
            let digest=expected_header_digests[slot];
            let mut digest_constants=vec![false;hash_boundary_rows.digest.len()];
            for term in &mut boundary.terms{
                if hash_boundary_rows.digest.contains(&term.row)
                    &&term.gate.c1.is_zero()&&term.gate.c2.is_zero()&&term.gate.c3.is_zero(){
                    let bit=term.row-hash_boundary_rows.digest.start;
                    term.gate.c0=-Fr::from(((digest[bit/8]>>(bit%8))&1) as u64);
                    digest_constants[bit]=true;
                }
            }
            assert!(digest_constants.iter().all(|seen|*seen),"slot {slot} digest constant map is incomplete");
            let (length_terms,length_rows)=crate::header_hash::canonical_length_padding_rows(
                &serializer.layout,hash_raws[slot].len(),hash_boundary_rows.global_padding.end).unwrap();
            assert_eq!(length_rows.len(),4_123);
            boundary.terms.extend(length_terms);
            assert_eq!(boundary.terms.len(),30_890);
            assert_eq!(work_tree_layout::hash_terms(&boundary.terms),hash_boundary_term_digests[slot],
                "slot {slot} streamed boundary differs from its reviewed materialization");
            (boundary,length_rows)
        };

        // Diagnose residuals per (slot,row). Reusing a local row across source
        // slots is intentional; folding those slots together could hide errors.
        let mut proof_row_residuals=BTreeMap::<(usize,usize),Fr>::new();
        for edge in &proof_edges{
            let left=value_at(edge.term.gate.left,&sparse_witness);
            let right=value_at(edge.term.gate.right,&sparse_witness);
            let residual=edge.term.gate.c0+edge.term.gate.c1*left+edge.term.gate.c2*right
                +edge.term.gate.c3*left*right;
            *proof_row_residuals.entry((edge.source_slot,edge.family_row)).or_insert(Fr::zero())
                +=residual;
        }
        assert!(proof_row_residuals.values().all(Zero::is_zero),
            "combined DAA and serializer projection witness has a nonzero row");

        let projection_edges=&proof_edges[baseline_edge_count..];
        let rejects_projection_mutation=|slot:usize,coordinate:usize,label:&str|{
            let mut changed=sparse_witness.clone();
            let value=value_at(coordinate,&changed);
            changed.insert(coordinate,if value.is_zero(){Fr::one()}else{Fr::zero()});
            let mut rows=BTreeMap::<usize,Fr>::new();
            for edge in projection_edges.iter().filter(|edge|edge.source_slot==slot){
                let left=value_at(edge.term.gate.left,&changed);
                let right=value_at(edge.term.gate.right,&changed);
                let residual=edge.term.gate.c0+edge.term.gate.c1*left+edge.term.gate.c2*right
                    +edge.term.gate.c3*left*right;
                *rows.entry(edge.family_row).or_insert(Fr::zero())+=residual;
            }
            assert!(rows.values().any(|residual|!residual.is_zero()),
                "combined committed projection accepted isolated {label} mutation");
        };
        let projection_slot=0usize;
        let timestamp_width=serializer.layout.fields.timestamp.iter()
            .rposition(|&wire|serialized[projection_slot][wire].is_one())
            .map_or(1,|bit|bit+1);
        let timestamp_length=(timestamp_width+6)/7;
        let n_bits_byte=130+32+timestamp_length;
        let height_byte=130+36+timestamp_length;
        rejects_projection_mutation(projection_slot,projection_slot*work_tree_layout::WIDTH
            +serializer_offset+serializer.layout.fields.timestamp[0],"timestamp field");
        rejects_projection_mutation(projection_slot,projection_slot*work_tree_layout::WIDTH
            +serializer_offset+serializer.layout.fields.n_bits[0],"nBits field");
        rejects_projection_mutation(projection_slot,projection_slot*work_tree_layout::WIDTH
            +serializer_offset+serializer.layout.fields.height[0],"height field");
        let projection_slots=serialized.len();
        drop(serialized);
        drop(fields);
        drop(hash_fields);
        drop(child_fields);
        rejects_projection_mutation(projection_slot,projection_slot*work_tree_layout::WIDTH
            +serializer_offset+serializer.layout.bytes[130][0],"timestamp output byte");
        rejects_projection_mutation(projection_slot,projection_slot*work_tree_layout::WIDTH
            +serializer_offset+serializer.layout.bytes[n_bits_byte][0],"nBits output byte");
        rejects_projection_mutation(projection_slot,projection_slot*work_tree_layout::WIDTH
            +serializer_offset+serializer.layout.bytes[height_byte][0],"height output byte");
        drop(rejects_projection_mutation);

        let mut proof_left_counts=vec![0usize;slots];
        let mut proof_right_counts=vec![0usize;slots];
        for edge in &proof_edges{
            proof_left_counts[edge.term.gate.left/work_tree_layout::WIDTH]+=1;
            proof_right_counts[edge.term.gate.right/work_tree_layout::WIDTH]+=1;
        }
        assert_eq!(proof_left_counts.iter().sum::<usize>(),proof_edges.len());
        assert_eq!(proof_right_counts.iter().sum::<usize>(),proof_edges.len());
        for left_endpoint in [true,false]{
            for slot in 0..slots{
                let expected=if left_endpoint{proof_left_counts[slot]}else{proof_right_counts[slot]};
                let mut streamed=0usize;
                edge_source.emit_endpoint(left_endpoint,slot,&mut |_|{streamed+=1;Ok(())}).unwrap();
                assert_eq!(streamed,expected,
                    "mature DAA streamed endpoint count differs: left={left_endpoint} slot={slot}");
            }
        }
        let proof_edge_wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|->Result<[Fr;4],String>{
            if r.len()!=21||u.len()!=24||v.len()!=24{
                return Err("combined DAA/projection wiring point dimension".into());
            }
            let mut out=[Fr::zero();4];
            for edge in &proof_edges{
                let row=(edge.source_slot<<17)|edge.family_row;
                let weight=crate::work_tree_wiring::eq_index(r,row)
                    *crate::work_tree_wiring::eq_index(u,edge.term.gate.left)
                    *crate::work_tree_wiring::eq_index(v,edge.term.gate.right);
                out[0]+=weight*edge.term.gate.c0;out[1]+=weight*edge.term.gate.c1;
                out[2]+=weight*edge.term.gate.c2;out[3]+=weight*edge.term.gate.c3;
            }
            Ok(out)
        };

        let total_started=std::time::Instant::now();
        // Bind the exact edge relation and the full 16-slot packed witness to
        // one transparent Dory commitment before deriving GKR challenges.
        use ark_serialize::CanonicalSerialize;
        let mut edge_hasher=Blake2bVar::new(32).unwrap();
        edge_hasher.update(b"nipopow-v2-daa-projected-canonical-edge-list-v1");
        edge_hasher.update(&(proof_edges.len() as u64).to_le_bytes());
        let mut scalar_bytes=Vec::with_capacity(32);
        for edge in &proof_edges{
            for coordinate in [edge.source_slot,edge.family_row,edge.term.row,
                edge.term.gate.left,edge.term.gate.right]{
                edge_hasher.update(&(coordinate as u64).to_le_bytes());
            }
            for coefficient in [edge.term.gate.c0,edge.term.gate.c1,
                edge.term.gate.c2,edge.term.gate.c3]{
                coefficient.serialize_compressed(&mut scalar_bytes).unwrap();
                edge_hasher.update(&scalar_bytes);
                scalar_bytes.clear();
            }
        }
        let mut edge_digest=[0u8;32];
        edge_hasher.finalize_variable(&mut edge_digest).unwrap();

        let packed_path=std::env::temp_dir().join(format!(
            "nipopow-v2-daa-k24-{}-{}.bits",std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let mut writer=crate::packed::PackedFileWriter::create_new(&packed_path,24).unwrap();
        let packed_cleanup=RemovePackedFixture(packed_path.clone());
        for slot in 0..slots{
            let first=slot*work_tree_layout::WIDTH;
            let mut bytes=vec![0u8;work_tree_layout::WIDTH/8];
            for (&coordinate,&value) in sparse_witness.range(first..first+work_tree_layout::WIDTH){
                assert!(value.is_zero()||value.is_one(),"committed DAA input must be Boolean");
                if value.is_one(){let local=coordinate-first;bytes[local/8]|=1<<(local%8);}
            }
            if slot<HASH_SLOT_COUNT{
                assert_eq!(hash_core_overlays[slot].len(),crate::header_hash::SERIALIZER_OFFSET/8);
                for (destination,&overlay) in bytes.iter_mut().zip(&hash_core_overlays[slot]){
                    *destination|=overlay;
                }
                for (index,&value) in hash_aux_overlays[slot].iter().enumerate(){
                    assert!(value<=1,"packed BLAKE auxiliary witness must be a bit");
                    if value==1{
                        let wire=crate::header_hash::AUX_OFFSET+index;
                        bytes[wire/8]|=1<<(wire%8);
                    }
                }
                if inventory_only&&slot==DAA_RESULT_SLOT{
                    // Private digest wires replace the public-digest constants
                    // in the production boundary used by the unified stream.
                    // This dedicated assignment receives a new commitment; it
                    // does not reuse the standard fixture commitment byte-for-byte.
                    for bit in 0..256{
                        let wire=crate::segment_relation::DIGEST_OFFSET+bit;
                        assert_eq!((bytes[wire/8]>>(wire%8))&1,0,
                            "private digest must occupy previously empty packed wires");
                        bytes[wire/8]|=((expected_header_digests[slot][bit/8]>>(bit%8))&1)
                            <<(wire%8);
                    }
                }
            }
            writer.write_bytes(&bytes).unwrap();
        }
        let source=writer.finish().unwrap();
        assert_eq!(source.input_len(),1usize<<24);
        drop(sparse_witness);
        drop(hash_core_overlays);
        drop(hash_aux_overlays);
        let setup_started=std::time::Instant::now();
        let setup=crate::pcs::generate_setup(24).unwrap();
        let setup_ms=setup_started.elapsed().as_millis();
        let commitment_started=std::time::Instant::now();
        let committed=crate::packed::commit(&source,&setup).unwrap();
        let commitment_bytes=crate::pcs::encode_commitment(&committed.commitment).unwrap();
        let commitment_ms=commitment_started.elapsed().as_millis();

        if inventory_only{
            diagnose_retained_three_family_stream(&edge_source,&proof_edges,&source,
                &setup.id,&commitment_bytes,&hash_raws,&expected_header_digests,
                opened.then_some((&setup,&committed)));
            // Both dedicated diagnostics return before the legacy proof roster.
            drop(source);
            std::fs::remove_file(&packed_path).unwrap();
            drop(packed_cleanup);
            return;
        }

        let domain=b"nipopow-v2-daa-projected-cross-slot-committed-gkr-dory-v1";
        let bind_test_statement_with_commitment=|transcript:&mut crate::transcript::Transcript,
            bound_commitment:&[u8]|{
            transcript.append_bytes(b"daa-edge-test-profile",b"mature-a1-a4-child-nbits-header-alias-and-field-projection-v1");
            transcript.append_bytes(b"fixture-scope",b"retained-mainnet-pre-eip-samples; synthetic computed EIP-shaped child at height 1153; timestamp-nBits-height projected to serializer bytes; slot9 child BLAKE2 recomputed after synthetic nBits under same commitment; schedule, ancestry, PoW and historical authentication excluded");
            transcript.append_u64(b"daa-result-slot",DAA_RESULT_SLOT as u64);
            transcript.append_u64(b"daa-edge-count",proof_edges.len() as u64);
            transcript.append_bytes(b"daa-edge-list-blake2b256",&edge_digest);
            transcript.append_bytes(b"pcs-setup-id",&setup.id);
            transcript.append_bytes(b"input-commitment",bound_commitment);
        };
        let bind_test_statement=|transcript:&mut crate::transcript::Transcript|{
            bind_test_statement_with_commitment(transcript,&commitment_bytes);
        };
        let mut prover_transcript=crate::transcript::Transcript::new(domain);
        let prove_started=std::time::Instant::now();
        let (proof,claim,incremental_u,incremental_v)=crate::sparse_stream_roster::prove_edge_terms(
            20,4,17,0,&[17],
            |left_endpoint,slot,sink|edge_source.emit_endpoint(left_endpoint,slot,sink),
            |slot|{
                if slot>=slots{return Err("packed DAA source slot outside input".into());}
                const CHUNK:usize=1<<16;
                let first=slot*(work_tree_layout::WIDTH/CHUNK);
                let mut copy=Vec::with_capacity(work_tree_layout::WIDTH);
                for chunk in 0..work_tree_layout::WIDTH/CHUNK{
                    copy.extend(source.read_copy(CHUNK,first+chunk)?);
                }
                Ok(copy)
            },
            &mut prover_transcript,bind_test_statement,
            |r,u,v|proof_edge_wiring(r,u,v),
        ).unwrap();
        let prove_elapsed=prove_started.elapsed();
        assert_eq!(proof.layers.len(),1);
        assert_eq!(proof.layers[0].rounds.len(),48);
        assert_eq!(proof.layers[0].line_coefficients.len(),25);
        assert_eq!(claim.point.len(),24);
        assert_eq!(source.evaluate(&claim.point).unwrap(),claim.value,
            "GKR input claim must evaluate against the committed packed witness");
        let encoded_proof=crate::gkr::encode_proof(&proof).unwrap();
        let decoded_proof=crate::gkr::decode_dimensions(&[24],&encoded_proof).unwrap();
        assert_eq!(decoded_proof,proof,"GKR wire proof must round-trip at the fixed relation shape");

        let mut verifier_transcript=crate::transcript::Transcript::new(domain);
        let verify_started=std::time::Instant::now();
        let verified=crate::gkr::verify_with_wiring(&[24],1usize<<21,&decoded_proof,&mut verifier_transcript,
            bind_test_statement,|_,r,u,v|proof_edge_wiring(r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension))
            .unwrap();
        let daa_gkr_verify_ms=verify_started.elapsed().as_millis();
        assert_eq!(verified,claim,"cross-slot DAA GKR verifier claim differs from the producer");
        assert_eq!(source.evaluate(&verified.point).unwrap(),verified.value,
            "DAA GKR claim must evaluate against the same packed commitment");

        let transcript_ledger=|t:&crate::transcript::Transcript|
            (t.challenges(),t.raw_queries(),t.bytes_absorbed());
        assert_eq!(transcript_ledger(&prover_transcript),transcript_ledger(&verifier_transcript),
            "DAA GKR-only prover and verifier transcripts must agree before PCS batching");
        let mut prover_continuation=prover_transcript.clone();
        let mut verifier_continuation=verifier_transcript.clone();
        assert_eq!(prover_continuation.try_challenge_scalar(b"daa-gkr-continuation").unwrap(),
            verifier_continuation.try_challenge_scalar(b"daa-gkr-continuation").unwrap(),
            "DAA GKR-only transcript continuations must agree");

        let mut wrong_commitment=commitment_bytes.clone();
        wrong_commitment[0]^=1;
        let mut wrong_commitment_transcript=crate::transcript::Transcript::new(domain);
        let wrong_commitment_result=crate::gkr::verify_with_wiring(&[24],1usize<<21,&decoded_proof,
            &mut wrong_commitment_transcript,
            |transcript|bind_test_statement_with_commitment(transcript,&wrong_commitment),
            |_,r,u,v|proof_edge_wiring(r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension));
        assert!(wrong_commitment_result.is_err(),
            "DAA GKR must reject when its bound packed commitment changes");

        let post_edge_proof_pipeline_ms=total_started.elapsed().as_millis();
        let daa_gkr_proof_bytes=encoded_proof.len();
        let daa_edge_count=proof_edges.len();
        let daa_claim=crate::opening_batch::Claim{point:verified.point.clone(),value:verified.value};

        // Release the large DAA edge roster before building per-header proofs.
        // Only verified claims cross this boundary.
        drop(proof_edge_wiring);
        drop(bind_test_statement);
        drop(bind_test_statement_with_commitment);
        drop(edge_source);
        drop(proof_left_counts);
        drop(proof_right_counts);
        drop(proof_edges);
        drop(decoded_proof);
        drop(proof);
        drop(claim);
        drop(encoded_proof);
        drop(prover_transcript);
        drop(verifier_transcript);
        drop(headers);
        drop(child_header);

        struct VerifiedRosterClaim{
            claim:crate::opening_batch::Claim,
            height:u32,
            slot:usize,
            role:&'static [u8],
            digest:[u8;32],
        }

        const LOG_N:usize=24;
        let hash_core_term_digest=work_tree_layout::hash_terms(&hash_core.terms);
        assert_eq!(hash_core.input_len,crate::header_hash::CORE_WIDTH);
        assert_eq!(hash_core.row_count,1<<17);
        assert_eq!(hash_core.terms.len(),172_480,"BLAKE compression term inventory changed");
        assert_eq!(hash_core.input_len*crate::header_hash::CORE_COPIES,
            crate::header_hash::SERIALIZER_OFFSET,"eight local compression copies must fill the committed core bank");

        let digest_for_slot=|slot:usize,override_digest:Option<(usize,[u8;32])>|->[u8;32]{
            match override_digest{
                Some((target,digest)) if target==slot=>digest,
                _=>expected_header_digests[slot],
            }
        };
        let append_hash_roster=|transcript:&mut crate::transcript::Transcript,
                                override_digest:Option<(usize,[u8;32])>|{
            transcript.append_bytes(b"header-hash-roster-profile",b"canonical-ergo-header-blake2b256-ten-slot-v1");
            transcript.append_bytes(b"active-slot-mask",&[0xff,0x03]);
            transcript.append_u64(b"active-header-count",HASH_SLOT_COUNT as u64);
            for slot in 0..HASH_SLOT_COUNT{
                let role:&[u8]=if slot==DAA_RESULT_SLOT{b"synthetic-child"}else{b"retained-mainnet"};
                transcript.append_u64(b"header-slot",slot as u64);
                transcript.append_bytes(b"header-role",role);
                transcript.append_u64(b"serialized-length",hash_raws[slot].len() as u64);
                transcript.append_bytes(b"expected-header-digest",&digest_for_slot(slot,override_digest));
                transcript.append_bytes(b"boundary-term-digest",hash_boundary_term_digests[slot].as_bytes());
            }
        };
        let append_hash_statement=|transcript:&mut crate::transcript::Transcript,slot:usize,role:&[u8],
                                   override_digest:Option<(usize,[u8;32])>|{
            append_hash_roster(transcript,override_digest);
            transcript.append_bytes(b"claim-role",role);
            transcript.append_u64(b"header-height",hash_heights[slot] as u64);
            transcript.append_u64(b"header-slot",slot as u64);
            transcript.append_u64(b"serialized-length",hash_raws[slot].len() as u64);
            transcript.append_bytes(b"expected-header-digest",&digest_for_slot(slot,override_digest));
            transcript.append_bytes(b"pcs-setup-id",&setup.id);
            transcript.append_bytes(b"input-commitment",&commitment_bytes);
        };
        let append_core_statement=|transcript:&mut crate::transcript::Transcript,slot:usize,role:&[u8],
                                   override_digest:Option<(usize,[u8;32])>|{
            append_hash_statement(transcript,slot,role,override_digest);
            transcript.append_u64(b"core-logical-copy-count",crate::header_hash::CORE_COPIES as u64);
            transcript.append_bytes(b"core-term-digest",hash_core_term_digest.as_bytes());
        };
        let append_boundary_statement=|transcript:&mut crate::transcript::Transcript,slot:usize,role:&[u8],
                                      override_digest:Option<(usize,[u8;32])>|{
            append_hash_statement(transcript,slot,role,override_digest);
            transcript.append_bytes(b"boundary-term-digest",hash_boundary_term_digests[slot].as_bytes());
            transcript.append_u64(b"boundary-term-count",30_890);
        };

        let core_domain=b"nipopow-v2-daa-log24-header-core-slot-gkr-v1";
        let boundary_domain=b"nipopow-v2-daa-log24-header-boundary-slot-gkr-v1";
        let mut roster_claims=Vec::<VerifiedRosterClaim>::with_capacity(1+2*HASH_SLOT_COUNT);
        roster_claims.push(VerifiedRosterClaim{
            claim:daa_claim,height:hash_heights[DAA_RESULT_SLOT],slot:DAA_RESULT_SLOT,
            role:b"daa-a1-a4-projection",digest:expected_header_digests[DAA_RESULT_SLOT],
        });
        let mut hash_gkr_proof_bytes=0usize;
        let mut hash_gkr_prove_ms=0u128;
        let mut hash_gkr_verify_ms=0u128;

        for slot in 0..HASH_SLOT_COUNT{
            let slot_input=read_packed_hash_slot(&source,slot,slots).unwrap();
            assert_eq!(slot_input.len(),work_tree_layout::WIDTH);

            let core_log_copies=crate::header_hash::CORE_COPIES.trailing_zeros() as usize;
            let mut core_prover=crate::transcript::Transcript::new(core_domain);
            append_core_statement(&mut core_prover,slot,b"blake2-core-eight-copies",None);
            let core_started=std::time::Instant::now();
            let (core_proof,core_claim)=crate::sparse::prove(
                &hash_core,&slot_input[..crate::header_hash::SERIALIZER_OFFSET],
                core_log_copies,&mut core_prover).unwrap();
            hash_gkr_prove_ms+=core_started.elapsed().as_millis();
            assert_eq!(core_claim.point.len(),19);
            let core_bytes=crate::gkr::encode_proof(&core_proof).unwrap();
            hash_gkr_proof_bytes+=core_bytes.len();
            let decoded_core=crate::sparse::decode_proof(&hash_core,core_log_copies,&core_bytes).unwrap();
            drop(core_proof);

            let mut core_verifier=crate::transcript::Transcript::new(core_domain);
            append_core_statement(&mut core_verifier,slot,b"blake2-core-eight-copies",None);
            let core_verify_started=std::time::Instant::now();
            let checked_core=crate::sparse::verify(
                &hash_core,core_log_copies,&decoded_core,&mut core_verifier).unwrap();
            hash_gkr_verify_ms+=core_verify_started.elapsed().as_millis();
            assert_eq!(checked_core,core_claim,"per-slot core GKR verifier claim");
            assert_eq!(checked_core.point.len(),19);

            let mut core_global_point=checked_core.point.clone();
            core_global_point.push(Fr::zero());
            for bit in 0..4{core_global_point.push(Fr::from(((slot>>bit)&1) as u64));}
            assert_eq!(core_global_point.len(),LOG_N);
            assert_eq!(source.evaluate(&core_global_point).unwrap(),checked_core.value,
                "per-slot core claim must embed at its exact global coordinates");
            if slot==0{
                assert_ne!(checked_core.value,Fr::zero(),
                    "active slot-0 core claim must distinguish the empty slot-10 control");
                let mut empty_slot_point=core_global_point.clone();
                for bit in 0..4{empty_slot_point[20+bit]=Fr::from(((10usize>>bit)&1) as u64);}
                assert_eq!(source.evaluate(&empty_slot_point).unwrap(),Fr::zero(),
                    "slot 10 must be a zero MLE opening in this 0..9 roster");

                let mut wrong_role=crate::transcript::Transcript::new(core_domain);
                append_core_statement(&mut wrong_role,slot,b"blake2-boundary",None);
                assert!(crate::sparse::verify(&hash_core,core_log_copies,&decoded_core,&mut wrong_role).is_err(),
                    "core proof must bind its role");

                let mut wrong_slot=crate::transcript::Transcript::new(core_domain);
                append_core_statement(&mut wrong_slot,slot+1,b"blake2-core-eight-copies",None);
                assert!(crate::sparse::verify(&hash_core,core_log_copies,&decoded_core,&mut wrong_slot).is_err(),
                    "core proof must bind its header slot");

                let mut wrong_digest=crate::transcript::Transcript::new(core_domain);
                append_core_statement(&mut wrong_digest,slot,b"blake2-core-eight-copies",Some((slot,[0xa5;32])));
                assert!(crate::sparse::verify(&hash_core,core_log_copies,&decoded_core,&mut wrong_digest).is_err(),
                    "core proof must bind its expected digest");
            }
            assert_eq!(transcript_ledger(&core_prover),transcript_ledger(&core_verifier),
                "per-slot core transcript ledger");
            let mut core_next=core_prover.clone();
            let mut core_verify_next=core_verifier.clone();
            assert_eq!(core_next.try_challenge_scalar(b"core-continuation").unwrap(),
                core_verify_next.try_challenge_scalar(b"core-continuation").unwrap());
            roster_claims.push(VerifiedRosterClaim{
                claim:crate::opening_batch::Claim{point:core_global_point,value:checked_core.value},
                height:hash_heights[slot],slot,role:b"blake2-core-eight-copies",
                digest:expected_header_digests[slot],
            });
            drop(decoded_core);
            drop(core_prover);
            drop(core_verifier);

            let (boundary_circuit,length_rows)=build_hash_boundary(slot);
            assert_eq!(length_rows.len(),4_123);
            assert_eq!(boundary_circuit.input_len,work_tree_layout::WIDTH);
            assert_eq!(boundary_circuit.row_count,1<<19);
            assert_eq!(boundary_circuit.terms.len(),30_890);
            let mut boundary_prover=crate::transcript::Transcript::new(boundary_domain);
            append_boundary_statement(&mut boundary_prover,slot,b"blake2-boundary-length-and-digest",None);
            let boundary_started=std::time::Instant::now();
            let (boundary_proof,boundary_claim)=crate::sparse::prove(
                &boundary_circuit,&slot_input,0,&mut boundary_prover).unwrap();
            hash_gkr_prove_ms+=boundary_started.elapsed().as_millis();
            assert_eq!(boundary_claim.point.len(),20);
            let boundary_bytes=crate::gkr::encode_proof(&boundary_proof).unwrap();
            hash_gkr_proof_bytes+=boundary_bytes.len();
            let decoded_boundary=crate::sparse::decode_proof(&boundary_circuit,0,&boundary_bytes).unwrap();
            drop(boundary_proof);

            let mut boundary_verifier=crate::transcript::Transcript::new(boundary_domain);
            append_boundary_statement(&mut boundary_verifier,slot,b"blake2-boundary-length-and-digest",None);
            let boundary_verify_started=std::time::Instant::now();
            let checked_boundary=crate::sparse::verify(
                &boundary_circuit,0,&decoded_boundary,&mut boundary_verifier).unwrap();
            hash_gkr_verify_ms+=boundary_verify_started.elapsed().as_millis();
            assert_eq!(checked_boundary,boundary_claim,"per-slot boundary GKR verifier claim");
            assert_eq!(checked_boundary.point.len(),20);
            let mut boundary_global_point=checked_boundary.point.clone();
            for bit in 0..4{boundary_global_point.push(Fr::from(((slot>>bit)&1) as u64));}
            assert_eq!(boundary_global_point.len(),LOG_N);
            assert_eq!(source.evaluate(&boundary_global_point).unwrap(),checked_boundary.value,
                "per-slot boundary claim must embed at its exact global coordinates");

            if slot==0{
                let mut wrong_digest=crate::transcript::Transcript::new(boundary_domain);
                append_boundary_statement(&mut wrong_digest,slot,
                    b"blake2-boundary-length-and-digest",Some((slot,[0xa5;32])));
                assert!(crate::sparse::verify(&boundary_circuit,0,&decoded_boundary,&mut wrong_digest).is_err(),
                    "boundary proof must bind its expected digest");
            }
            assert_eq!(transcript_ledger(&boundary_prover),transcript_ledger(&boundary_verifier),
                "per-slot boundary transcript ledger");
            let mut boundary_next=boundary_prover.clone();
            let mut boundary_verify_next=boundary_verifier.clone();
            assert_eq!(boundary_next.try_challenge_scalar(b"boundary-continuation").unwrap(),
                boundary_verify_next.try_challenge_scalar(b"boundary-continuation").unwrap());
            roster_claims.push(VerifiedRosterClaim{
                claim:crate::opening_batch::Claim{point:boundary_global_point,value:checked_boundary.value},
                height:hash_heights[slot],slot,role:b"blake2-boundary-length-and-digest",
                digest:expected_header_digests[slot],
            });
            drop(decoded_boundary);
            drop(boundary_prover);
            drop(boundary_verifier);
            drop(boundary_circuit);
            drop(slot_input);
        }

        assert_eq!(roster_claims.len(),1+2*HASH_SLOT_COUNT,
            "roster must contain one DAA claim and exactly one core/boundary claim per header");
        assert_eq!(roster_claims[0].role,b"daa-a1-a4-projection");
        for slot in 0..HASH_SLOT_COUNT{
            let first=1+2*slot;
            assert_eq!((roster_claims[first].slot,roster_claims[first].role),
                (slot,b"blake2-core-eight-copies".as_slice()),"missing or duplicated core obligation for slot {slot}");
            assert_eq!((roster_claims[first+1].slot,roster_claims[first+1].role),
                (slot,b"blake2-boundary-length-and-digest".as_slice()),
                "missing or duplicated boundary obligation for slot {slot}");
        }

        let mut batch_packet_sizes=Vec::with_capacity(3);
        let mut batch_packets=Vec::<Vec<u8>>::with_capacity(3);
        let mut batch_statements=Vec::<crate::opening_batch::Statement>::with_capacity(3);
        let mut batch_metrics_projection=0.0f64;
        let mut batch_metrics_transition=0.0f64;
        let mut batch_metrics_pcs=0.0f64;
        let mut batch_metrics_projection_scans=0usize;
        let mut batch_metrics_transition_scans=0usize;
        let mut batch_prove_ms=0u128;
        let mut batch_verify_ms=0u128;
        for batch_index in 0..3{
            let start=batch_index*crate::opening_batch::CLAIMS;
            let end=start+crate::opening_batch::CLAIMS;
            let members=&roster_claims[start..end];
            assert_eq!(members.len(),crate::opening_batch::CLAIMS,
                "21 obligations must form three full batches without repeated padding");
            let claims:[crate::opening_batch::Claim;crate::opening_batch::CLAIMS]=
                members.iter().map(|entry|entry.claim.clone()).collect::<Vec<_>>().try_into().unwrap();
            let mut corpus=b"nipopow-v2-daa-ten-header-shared-log24-opening-batch-v1\0".to_vec();
            corpus.extend_from_slice(&setup.id);
            corpus.extend_from_slice(&commitment_bytes);
            corpus.extend_from_slice(&(batch_index as u64).to_le_bytes());
            for (offset,entry) in members.iter().enumerate(){
                corpus.extend_from_slice(&((start+offset) as u64).to_le_bytes());
                corpus.extend_from_slice(&entry.height.to_le_bytes());
                corpus.extend_from_slice(&(entry.slot as u64).to_le_bytes());
                corpus.extend_from_slice(&(entry.role.len() as u64).to_le_bytes());
                corpus.extend_from_slice(entry.role);
                corpus.extend_from_slice(&entry.digest);
            }
            let statement=crate::opening_batch::Statement{
                log_n:LOG_N,setup_id:setup.id,commitment:committed.commitment.clone(),
                corpus_id:Some(ergo_header_core::blake2b256(&corpus)),claims,
            };
            let started=std::time::Instant::now();
            let (proof,metrics,producer_transcript)=crate::opening_batch::prove(
                &source,&committed,&setup,&statement).unwrap();
            let packet=crate::opening_batch::encode_proof(&proof,LOG_N).unwrap();
            let decoded=crate::opening_batch::decode_proof(&packet,LOG_N).unwrap();
            assert_eq!(crate::opening_batch::encode_proof(&decoded,LOG_N).unwrap(),packet,
                "opening batch encoding must round-trip canonically");
            batch_prove_ms+=started.elapsed().as_millis();
            batch_packet_sizes.push(packet.len());
            batch_metrics_projection+=metrics.projection_seconds;
            batch_metrics_transition+=metrics.transition_seconds;
            batch_metrics_pcs+=metrics.pcs_seconds;
            batch_metrics_projection_scans+=metrics.projection_scans;
            batch_metrics_transition_scans+=metrics.transition_scans;

            let started=std::time::Instant::now();
            let verifier_transcript=crate::opening_batch::verify(&statement,&setup,&decoded).unwrap();
            batch_verify_ms+=started.elapsed().as_millis();
            assert_eq!(transcript_ledger(&producer_transcript),transcript_ledger(&verifier_transcript),
                "opening batch prover/verifier ledger must match");
            let mut producer_next=producer_transcript.clone();
            let mut verifier_next=verifier_transcript.clone();
            assert_eq!(producer_next.try_challenge_scalar(b"batch-continuation").unwrap(),
                verifier_next.try_challenge_scalar(b"batch-continuation").unwrap());

            if batch_index==0{
                let mut wrong_slot=statement.clone();
                for bit in 0..4{
                    wrong_slot.claims[1].point[20+bit]=Fr::from(((10usize>>bit)&1) as u64);
                }
                assert_eq!(source.evaluate(&wrong_slot.claims[1].point).unwrap(),Fr::zero(),
                    "the moved core claim must evaluate to zero in empty slot 10");
                assert_ne!(wrong_slot.claims[1].value,Fr::zero());
                assert!(crate::opening_batch::verify(&wrong_slot,&setup,&decoded).is_err(),
                    "batch must reject a core opening moved from slot 0 to empty slot 10");

                let mut wrong_roles=statement.clone();
                wrong_roles.claims.swap(1,2);
                assert!(crate::opening_batch::verify(&wrong_roles,&setup,&decoded).is_err(),
                    "batch must reject a core/boundary role permutation");

                let mut wrong_corpus=statement.clone();
                wrong_corpus.corpus_id=Some([0x5a;32]);
                assert!(crate::opening_batch::verify(&wrong_corpus,&setup,&decoded).is_err(),
                    "batch must reject a changed roster corpus");

                let mut wrong_commitment=statement.clone();
                wrong_commitment.commitment=setup.prover.ht;
                assert_ne!(crate::pcs::encode_commitment(&wrong_commitment.commitment).unwrap(),commitment_bytes,
                    "commitment mutant must be distinct");
                assert!(crate::opening_batch::verify(&wrong_commitment,&setup,&decoded).is_err(),
                    "batch must reject a changed commitment");
            }
            batch_statements.push(statement);
            batch_packets.push(packet);
            drop(proof);
            drop(decoded);
            drop(producer_transcript);
            drop(verifier_transcript);
        }

        assert_eq!(batch_packets.len(),3,"all three seven-claim opening batches are required");
        let wrong_batch_packet=crate::opening_batch::decode_proof(&batch_packets[1],LOG_N).unwrap();
        assert!(crate::opening_batch::verify(&batch_statements[0],&setup,&wrong_batch_packet).is_err(),
            "a packet from batch 1 must not verify as batch 0");

        let batch_bytes:usize=batch_packet_sizes.iter().sum();
        println!("DAA+header shared log24 GKR-Dory: active_slots=0..9, gkr_claims=21, batches=3x7, daa_gkr_bytes={}, header_gkr_bytes={}, batch_packet_sizes={:?}, batch_bytes={}, total_proof_bytes={}, setup_ms={}, packed_commit_ms={}, daa_gkr_prover_ms={}, daa_gkr_verify_ms={}, header_gkr_prover_ms={}, header_gkr_verify_ms={}, batch_prove_encode_decode_ms={}, batch_verify_ms={}, projection_scans={}, transition_scans={}, projection_s={}, transition_s={}, pcs_s={}, slot10_empty_mutant=rejected, role_swap_mutant=rejected, changed_digest_mutants=rejected, commitment_mutant=rejected, wrong_batch_packet=rejected, result=pass",
            daa_gkr_proof_bytes,hash_gkr_proof_bytes,batch_packet_sizes,batch_bytes,
            daa_gkr_proof_bytes+hash_gkr_proof_bytes+batch_bytes,setup_ms,commitment_ms,prove_elapsed.as_millis(),
            daa_gkr_verify_ms,hash_gkr_prove_ms,hash_gkr_verify_ms,batch_prove_ms,batch_verify_ms,
            batch_metrics_projection_scans,batch_metrics_transition_scans,batch_metrics_projection,
            batch_metrics_transition,batch_metrics_pcs);
        println!("DAA projected GKR: edges={}, projection_slots={}, projection_terms={}, slots=16, input_log2=24, rows=2^21, gkr_bytes={}, gkr_prover_ms={}, gkr_verify_ms={}, pipeline_ms={}, incremental_u={}, incremental_v={}, result=pass",
            daa_edge_count,projection_slots,projection_terms,daa_gkr_proof_bytes,
            prove_elapsed.as_millis(),daa_gkr_verify_ms,post_edge_proof_pipeline_ms,incremental_u,incremental_v);
        println!("DAA cross-slot edge differential: edges={}, input_bits=24, row_bits=21, left/right endpoints exact, residuals exact, coefficient differential exact",baseline_edge_count);
        drop(source);
        std::fs::remove_file(&packed_path).unwrap();
        drop(packed_cleanup);
        assert!(!packed_path.exists(),"packed DAA test fixture must be removed");
    }
}
