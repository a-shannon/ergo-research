//! Exact generic/Boolean residual differentials on actual canonical traces.
//! These local assignments issue no source, history or proof authority.
use super::*;
use std::collections::BTreeSet;

fn recover(values:&BTreeMap<usize,Fr>,offset:usize) -> Vec<Fr> {
    let mut trace=vec![Fr::zero();CORE];
    for (&wire,&value) in values.range(offset..offset+CORE) {trace[wire-offset]=value;}
    trace
}
fn exact_boolean_verdict(e:&Engine,input:&[Fr]) -> Result<(),String> {
    let expected=verify_core_generic(e,input);
    let bits=checked_boolean_view(input).ok_or("canonical trace was not Boolean")?;
    assert_eq!(bits.len(),CORE);assert_eq!(std::mem::size_of::<bool>(),1);
    assert_eq!(bits.len()*std::mem::size_of::<bool>(),65_536);
    assert_eq!(verify_core_boolean(e,&bits),expected);
    assert_eq!(verify_core(e,input),expected);
    expected
}
fn trace_digest(e:&Engine,input:&[Fr]) -> [u8;32] {
    let mut bytes=[0u8;32];
    for bit in 0..256 {
        if input[e.base.compression.output[bit/64][bit%64]].is_one() {bytes[bit/8]|=1<<(bit%8);}
    }
    bytes
}
fn trace_output(e:&Engine,input:&[Fr]) -> [Fr;512] {
    std::array::from_fn(|bit|input[e.base.compression.output[bit/64][bit%64]])
}
fn work_profile_hash() -> [u8;32] {
    let mut bytes=fixed::PROFILE_PREFIX.to_vec();bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
    assert_eq!(bytes.len(),59);hash(&bytes)
}
fn compression_assignment(e:&Engine) -> Result<circuit::CompressionAssignment,String> {
    let input=CompressionInput {state:circuit::blake2b256_initial_state(),
        block:std::array::from_fn(|i|(i as u8).wrapping_mul(29).wrapping_add(7)),counter:128,final_flag:true};
    let assigned=circuit::assign_compression(&input,&e.base.compression,CORE)?;
    assert_eq!(assigned.layout,e.base.compression);assert_eq!(digest(assigned.output),hash(&input.block));
    Ok(assigned)
}

#[test]
fn c599_actual_chained_leaf_padding_and_dummy_cores_match_generic() -> Result<(),String> {
    let e=fixed::engine()?;let raw=include_bytes!("../fixtures/mainnet-daa-child-4097-v1.raw.bin");
    let header=ergo_header_core::Header::decode(raw,None).map_err(|error|format!("fixture header decode: {error:?}"))?;
    assert_eq!(header.height,4097);assert_eq!(header.encode().map_err(|e|format!("{e:?}"))?,raw);
    let profile=work_profile_hash();let mut upper=[0u8;28];upper[27]=1;
    let p=LeafProfile::new(4097,[0x31;32])?;let boundary=compile(e,p.clone())?;
    let assigned=assign_header_leaf(e,&boundary,4095,&header,[0;28],upper,profile)?;
    assert_eq!(assigned.digest,native_leaf_preimage_hash(&p,4095,raw,4097,[0;28],upper,profile)?);
    let last=(99+raw.len()-1)/128;assert_eq!(last,2);
    let mut previous:Option<[Fr;512]>=None;
    for copy in 0..5 {
        let trace=recover(&assigned.values,CORES[copy]);exact_boolean_verdict(e,&trace)?;
        if copy==1 {
            let prior=previous.as_ref().ok_or("missing chained compression output")?;
            for bit in 0..512 {assert_eq!(trace[e.base.compression.state[bit/64][bit%64]],prior[bit]);}
        }
        if copy==last {assert_eq!(trace_digest(e,&trace),assigned.digest);}
        if copy>last {assert_eq!(trace_digest(e,&trace),hash(&[]));}
        previous=Some(trace_output(e,&trace));
    }
    drop(assigned);drop(boundary);
    let padding=LeafProfile::new(4098,[0x31;32])?;let boundary=compile(e,padding.clone())?;
    assert_eq!(padding.role(4097)?,Role::Padding);
    let assigned=assign_inactive_leaf(e,&boundary,4097,profile)?;
    let envelope=Envelope {raw:Vec::new(),height:0,lower:[0;28],upper:[0;28],profile};
    assert_eq!(assigned.digest,native_digest(&padding,4097,&envelope)?);
    for copy in 0..5 {
        let trace=recover(&assigned.values,CORES[copy]);exact_boolean_verdict(e,&trace)?;
        assert_eq!(trace_digest(e,&trace),if copy==0 {assigned.digest}else{hash(&[])});
    }
    drop(assigned);drop(boundary);
    let dummy=compile(e,p.clone())?;assert_eq!(p.role(4096)?,Role::Dummy);
    let assigned=assign_inactive_leaf(e,&dummy,4096,profile)?;
    assert_eq!(assigned.digest,[0;32],"dummy leaf has no active digest endpoint");
    for copy in 0..5 {
        let trace=recover(&assigned.values,CORES[copy]);exact_boolean_verdict(e,&trace)?;
        assert_eq!(trace_digest(e,&trace),hash(&[]));
    }
    Ok(())
}

#[test]
fn c599_actual_fixed_node_profile_and_dummy_cores_match_native_hashes() -> Result<(),String> {
    let e=fixed::engine()?;let profile=fixed::FixedProfile::new(4097,[0x31;32])?;
    let mut node=vec![b'N',1];node.extend_from_slice(&0u32.to_be_bytes());
    node.extend_from_slice(&[0x45;32]);node.extend_from_slice(&[0x92;32]);assert_eq!(node.len(),70);
    let mut profile_bytes=profile.prefix.clone();profile_bytes.extend_from_slice(&profile.genesis);assert_eq!(profile_bytes.len(),59);
    let cases=[(profile.tree.level(1)?.0,node),(profile.tree.profile_node_slot,profile_bytes),(profile.tree.leaves,Vec::new())];
    for (slot,bytes) in cases {
        let assigned=assign_fixed_slot_native(e,&profile,slot,&bytes)?;
        let trace=recover(&assigned.values,fixed::NODE_CORE);exact_boolean_verdict(e,&trace)?;
        let expected=native_fixed_preimage_hash(&profile,slot,&bytes)?;
        assert_eq!(assigned.digest,expected);assert_eq!(trace_digest(e,&trace),expected);
    }
    Ok(())
}

#[test]
fn c599_isolated_boolean_and_nonboolean_core_mutants_preserve_exact_verdicts() -> Result<(),String> {
    let e=fixed::engine()?;let assigned=compression_assignment(e)?;exact_boolean_verdict(e,&assigned.input)?;
    let l=&assigned.layout;
    let protected=l.state.iter().flatten().chain(l.message.iter().flatten()).chain(l.counter.iter())
        .chain(std::iter::once(&l.final_flag)).chain(l.output.iter().flatten()).copied().collect::<BTreeSet<_>>();
    let intermediate=(l.final_flag+1..l.used_input_len).find(|wire|!protected.contains(wire))
        .ok_or("canonical core has no private operation coordinate")?;
    let coordinates=[l.state[0][0],l.message[3][7],l.counter[63],l.final_flag,intermediate,l.output[7][63],0,CORE-1];
    for wire in coordinates {
        let mut changed=assigned.input.clone();changed[wire]=Fr::one()-changed[wire];
        let reference=verify_core_generic(e,&changed);
        let bits=checked_boolean_view(&changed).ok_or("Boolean mutation lost its original view")?;
        assert_eq!(verify_core_boolean(e,&bits),reference,"Boolean wire {wire}");
        assert_eq!(verify_core(e,&changed),reference,"Boolean dispatch wire {wire}");
        // Some unused Boolean coordinates may be accepted. Exact equality,
        // including the first residual error, is the required invariant.
        for value in [Fr::from(2u64),-Fr::one(),Fr::from(123_457u64)] {
            let mut changed=assigned.input.clone();changed[wire]=value;
            assert!(checked_boolean_view(&changed).is_none(),"nonboolean original wire {wire}");
            assert_eq!(verify_core(e,&changed),verify_core_generic(e,&changed),"Fr fallback wire {wire}");
        }
    }
    let mut referenced=vec![false;CORE];
    for term in &e.core.terms {referenced[term.gate.left]=true;referenced[term.gate.right]=true;}
    if let Some(unused)=(l.used_input_len..CORE).find(|wire|!referenced[*wire]) {
        let mut changed=assigned.input.clone();changed[unused]=Fr::from(2u64);
        assert!(checked_boolean_view(&changed).is_none());
        assert_eq!(verify_core_generic(e,&changed),Ok(()));assert_eq!(verify_core(e,&changed),Ok(()));
    } else {
        assert!((l.used_input_len..CORE).all(|wire|referenced[wire]),"no unreferenced padding coordinate exists in this core");
    }
    Ok(())
}

#[test]
fn c599_complete_original_boolean_view_and_width_guards_preserve_generic_errors() -> Result<(),String> {
    let e=fixed::engine()?;let assigned=compression_assignment(e)?;
    assert!(assigned.layout.used_input_len<CORE);
    let mut nonboolean_padding=assigned.input.clone();nonboolean_padding[CORE-1]=Fr::from(2u64);
    assert!(checked_boolean_view(&nonboolean_padding).is_none(),"the last original coordinate must be scanned");
    assert_eq!(verify_core(e,&nonboolean_padding),verify_core_generic(e,&nonboolean_padding));
    for width in [0,CORE-1,CORE+1] {
        let input=vec![Fr::zero();width];assert!(checked_boolean_view(&input).is_none());
        let expected=Err("leaf compression witness width".to_string());
        assert_eq!(verify_core_generic(e,&input),expected);assert_eq!(verify_core(e,&input),expected);
        assert_eq!(verify_core_boolean(e,&vec![false;width]),expected);
    }
    for pattern in 0..4 {
        let bits=(0..CORE).map(|wire|match pattern {0=>false,1=>true,2=>wire%2==0,
            _=>(wire.wrapping_mul(17).wrapping_add(wire/7))%11<5}).collect::<Vec<_>>();
        let input=bits.iter().map(|bit|Fr::from(*bit as u64)).collect::<Vec<_>>();
        assert_eq!(checked_boolean_view(&input),Some(bits.clone()));
        let reference=verify_core_generic(e,&input);
        assert_eq!(verify_core_boolean(e,&bits),reference);assert_eq!(verify_core(e,&input),reference);
    }
    Ok(())
}
