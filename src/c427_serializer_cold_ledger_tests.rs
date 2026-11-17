use super::*;
use ark_ff::{BigInteger,One,PrimeField,Zero};

const C427_PRECODE_SHA256:&str="DBBB738987A14537A3F9A3660C1378C8BADA6C2A67B32502587D6EC15A4FB7B8";
const C425_PRECODE_SHA256:&str="C0AAB1897204EFCDC472D09F77922345326E184DB183B7FDD7DD6EEAF34C4BD1";
const C423_PRECODE_SHA256:&str="55EF77CA39A3E9299FD4262B2EB83F98D0473E981ECC2BE605A3D9BC8AF86AB3";
const C397_SOURCE_CLOSURE_SHA256:&str="50B0A3A03482F58B02AE37C1C9710E40986C014A2ECD5597248E34CF5D52CC9A";
const C220_PRECODE_SHA256:&str="AF9C09C5D2DDCF283441D3621BA3EAD6DCF42C440121326EACEC76A27B691623";
const BOOLEAN_TERMS:usize=69_680;
const PADDING_TERMS:usize=61_392;
const FAMILY_TERMS:usize=131_072;
const SERIALIZER_ROW_BASE:usize=22_756;
const ATTACHED_ROW_OFFSET:usize=12_836;
const SERIALIZER_WIRE_BASE:usize=524_288;

fn canonical_family()->(Vec<Term>,Vec<&'static str>,Vec<Option<crate::c425_span_census::SerializerFamilyOrigin>>) {
    let (terms,spans)=super::canonical();
    let origins=crate::c425_span_census::finish_source_family_origins();
    assert_eq!(terms.len(),474_755);
    assert_eq!(spans.len(),terms.len());
    assert_eq!(origins.len(),terms.len());
    (terms,spans,origins)
}

fn family_counts(tagged:&[Tagged],origins:&[Option<crate::c425_span_census::SerializerFamilyOrigin>])
    ->BTreeMap<&'static str,usize> {
    let mut counts=BTreeMap::new();
    for item in tagged {
        if let Some(origin)=origins.get(item.ordinal).copied().flatten() {
            *counts.entry(origin.label).or_default()+=1;
        }
    }
    counts
}

fn family_items(tagged:&[Tagged],origins:&[Option<crate::c425_span_census::SerializerFamilyOrigin>])
    ->Vec<Tagged> {
    tagged.iter().filter(|item|origins.get(item.ordinal).is_some_and(Option::is_some))
        .cloned().collect()
}

fn assert_family_ledger(terms:&[Term],spans:&[&str],origins:&[Option<crate::c425_span_census::SerializerFamilyOrigin>]) {
    let mut counts=BTreeMap::<&str,usize>::new();
    let mut previous_global=None;
    let mut previous_source=None;
    let mut next_boolean=0usize;
    let mut next_padding=0usize;
    let mut source_to_global_offset=None;
    for (global_ordinal,origin) in origins.iter().copied().enumerate() {
        let Some(origin)=origin else {continue};
        assert_eq!(spans[global_ordinal],"serializer.attach",
            "C427 family label escaped the C425 attachment at global ordinal {global_ordinal}");
        assert!(previous_global.map_or(true,|previous|previous<global_ordinal),
            "C427 global family ordinals are not strictly increasing at {global_ordinal}");
        assert!(previous_source.map_or(true,|previous|previous<origin.serializer_term_ordinal),
            "C427 Builder term ordinals are not strictly increasing at {global_ordinal}");
        if let (Some(previous_global),Some(previous_source))=(previous_global,previous_source) {
            assert_eq!(global_ordinal,previous_global+1,
                "C427 family global occurrence gap after {previous_global}");
            assert_eq!(origin.serializer_term_ordinal,previous_source+1,
                "C427 Builder family occurrence gap after source ordinal {previous_source}");
        }
        let offset=global_ordinal.checked_sub(origin.serializer_term_ordinal)
            .expect("C427 global ordinal precedes serializer term ordinal");
        assert!(source_to_global_offset.replace(offset).map_or(true,|prior|prior==offset),
            "C427 attachment source-order mapping is not a fixed offset");
        let family_index=match origin.label {
            "serializer_boolean_diagonal"=>{
                assert_eq!(origin.family_ordinal,next_boolean,"C427 Boolean callsite ordinal gap");
                next_boolean+=1;origin.family_ordinal
            }
            "serializer_input_padding"=>{
                assert_eq!(origin.family_ordinal,next_padding,"C427 padding callsite ordinal gap");
                next_padding+=1;BOOLEAN_TERMS+origin.family_ordinal
            }
            other=>panic!("C427 unclassified source callsite label {other}"),
        };
        let expected=Term {row:ATTACHED_ROW_OFFSET+SERIALIZER_ROW_BASE+family_index,
            gate:crate::gkr::Gate {
                left:SERIALIZER_WIRE_BASE+family_index,
                right:if family_index<BOOLEAN_TERMS {SERIALIZER_WIRE_BASE+family_index} else {SERIALIZER_WIRE_BASE},
                c0:Fr::zero(),
                c1:if family_index<BOOLEAN_TERMS {-Fr::one()} else {Fr::one()},
                c2:Fr::zero(),
                c3:if family_index<BOOLEAN_TERMS {Fr::one()} else {Fr::zero()},
            }};
        if terms[global_ordinal]!=expected {
            panic!("C427 family first literal tuple divergence global_ordinal={global_ordinal} serializer_term_ordinal={} label={} family_ordinal={} expected={:?} observed={:?}",
                origin.serializer_term_ordinal,origin.label,origin.family_ordinal,
                crate::c425_span_census::tuple(&expected),crate::c425_span_census::tuple(&terms[global_ordinal]));
        }
        *counts.entry(origin.label).or_default()+=1;
        previous_global=Some(global_ordinal);
        previous_source=Some(origin.serializer_term_ordinal);
    }
    assert_eq!(counts.get("serializer_boolean_diagonal"),Some(&BOOLEAN_TERMS));
    assert_eq!(counts.get("serializer_input_padding"),Some(&PADDING_TERMS));
    assert_eq!(counts.values().sum::<usize>(),FAMILY_TERMS);
    assert_eq!(next_boolean,BOOLEAN_TERMS);
    assert_eq!(next_padding,PADDING_TERMS);
}

#[test]
fn c427_serializer_builder_family_callsite_cold_ledger() {
    let (terms,spans,origins)=canonical_family();
    assert_family_ledger(&terms,&spans,&origins);
    let first=origins.iter().position(Option::is_some).unwrap();
    let last=origins.iter().rposition(Option::is_some).unwrap();
    let first_origin=origins[first].unwrap();
    let last_origin=origins[last].unwrap();
    println!("C427 cold source ledger PRECODE={C427_PRECODE_SHA256} C425_PRECODE={C425_PRECODE_SHA256} C423_PRECODE={C423_PRECODE_SHA256} C220_PRECODE={C220_PRECODE_SHA256} C397={C397_SOURCE_CLOSURE_SHA256} canonical_terms={} family_terms={} boolean={} padding={} global_ordinals={first}..={last} serializer_term_ordinals={}..={} source_labels=builder_callsites literal_tuple_order=passed-if-test-green",
        terms.len(),FAMILY_TERMS,BOOLEAN_TERMS,PADDING_TERMS,
        first_origin.serializer_term_ordinal,last_origin.serializer_term_ordinal);
}

fn cold_owner_family_census(
    owner:usize,
    expected_class:OwnerClass,
    expected_active:[bool;4],
    parent:&WorkTreeHistoryPlan,
    roster:&DaaHistoryRoster<'_>,
    row_plan:&RowPlan<'_,'_>,
    canonical:&[Term],
    spans:&[&str],
    origins:&[Option<crate::c425_span_census::SerializerFamilyOrigin>],
) -> Vec<Tagged> {
    assert_eq!(roster.owner_class(owner as u64).unwrap(),expected_class,"C427 owner class {owner}");
    let schedule=Scheduled::eligible08();
    let active=source_active_mask(&schedule,owner).unwrap();
    assert_eq!(active,expected_active,"C427 independently derived owner mask {owner}");

    let (base,base_counts)={
        let mut output=Vec::new();
        let counts=parent.header_boundary().visit_slot_terms(owner as u64,|term|{
            let ordinal=crate::c425_span_census::current_source_ordinal()
                .ok_or("C427 base callback lost direct source ordinal")?;
            output.push(Tagged{ordinal,term});Ok(())
        }).unwrap_or_else(|error|panic!("C427 base owner={owner}: {error}"));
        (output,counts)
    };
    validate_tagged(owner,canonical,spans,&base,"C427 base/mature-A4").unwrap();
    let mut work_tree=Vec::new();
    let work_counts=parent.visit_slot_terms(owner as u64,|term|{
        let ordinal=crate::c425_span_census::current_source_ordinal()
            .ok_or("C427 WorkTree callback lost direct source ordinal")?;
        work_tree.push(Tagged{ordinal,term});Ok(())
    }).unwrap_or_else(|error|panic!("C427 WorkTree owner={owner}: {error}"));
    validate_tagged(owner,canonical,spans,&work_tree,"C427 WorkTree").unwrap();
    let worktree_drops=dropped_by_span(&base,&work_tree,spans,"C427 WorkTree").unwrap();
    assert_eq!(worktree_drops.values().sum::<usize>(),work_counts.omitted_worktree,
        "C427 WorkTree source flags vs direct ordinal retirement owner={owner}");

    let mut rostered=Vec::new();
    let roster_counts=roster.visit_header_terms(owner as u64,|term|{
        let ordinal=crate::c425_span_census::current_source_ordinal()
            .ok_or("C427 DaaRoster callback lost direct source ordinal")?;
        rostered.push(Tagged{ordinal,term});Ok(())
    }).unwrap_or_else(|error|panic!("C427 DaaRoster owner={owner}: {error}"));
    validate_tagged(owner,canonical,spans,&rostered,"C427 DaaRoster").unwrap();
    let short_drops=dropped_by_span(&work_tree,&rostered,spans,"C427 short-A4").unwrap();
    assert_eq!(short_drops.values().sum::<usize>(),roster_counts.omitted_short_a4,
        "C427 short-A4 source flags vs direct ordinal retirement owner={owner}");
    assert_eq!(roster_counts.emitted,rostered.len(),"C427 DaaRoster emitted counter owner={owner}");
    assert_eq!(roster_counts.omitted_worktree,work_counts.omitted_worktree,
        "C427 DaaRoster/WorkTree retirement counter owner={owner}");
    assert_eq!(roster_counts.omitted_mature_a4,base_counts.omitted_a4,
        "C427 DaaRoster/base mature-A4 counter owner={owner}");
    assert_eq!(work_counts.omitted_a4,base_counts.omitted_a4,
        "C427 WorkTree/base mature-A4 counter owner={owner}");
    assert_eq!(base.len()+base_counts.omitted_a4,canonical.len(),
        "C427 base emitted plus mature-A4 omitted owner={owner}");

    let source_family=family_items(&rostered,origins);
    let (scheduled,retired)=scheduled_filter(owner,active,&rostered)
        .unwrap_or_else(|error|panic!("C427 scheduled source predicate owner={owner}: {error}"));
    let scheduled_drops=dropped_by_span(&rostered,&scheduled,spans,"C427 scheduled").unwrap();
    assert_eq!(scheduled_drops.values().sum::<usize>(),retired.iter().sum::<usize>(),
        "C427 scheduled source flags vs direct ordinal retirement owner={owner}");
    let scheduled_family=family_items(&scheduled,origins);
    let native=row_plan.header.header_terms(owner).unwrap();
    let candidate_terms=scheduled.iter().map(|item|item.term.clone()).collect::<Vec<_>>();
    let candidate_ordinals=scheduled.iter().map(|item|item.ordinal).collect::<Vec<_>>();
    compare_terms(&candidate_terms,&native.terms,Some(&candidate_ordinals),Some(spans),
        "C427 candidate/native Merge full HEADER");
    assert_eq!(retired,native.retired,"C427 Merge retirement counters owner={owner}");
    validate_tagged(owner,canonical,spans,&scheduled_family,"C427 scheduled family").unwrap();

    let scheduled_family_positions=scheduled.iter().enumerate().filter_map(|(index,item)|
        origins.get(item.ordinal).is_some_and(Option::is_some).then_some(index)).collect::<Vec<_>>();
    let native_family=scheduled_family_positions.iter().map(|&index|Tagged{
        ordinal:scheduled[index].ordinal,term:native.terms[index].clone(),
    }).collect::<Vec<_>>();
    compare_terms(
        &scheduled_family.iter().map(|item|item.term.clone()).collect::<Vec<_>>(),
        &native_family.iter().map(|item|item.term.clone()).collect::<Vec<_>>(),
        Some(&native_family.iter().map(|item|item.ordinal).collect::<Vec<_>>()),
        Some(spans),"C427 source-labelled family/native Merge ordered projection");

    let batch=row_plan.stage_owner(owner).unwrap();
    let native_placed=row_plan.check_raw_header_placement(owner,&candidate_terms,&batch).unwrap();
    let mut family_placed=Vec::with_capacity(scheduled_family.len());
    for (position,item) in scheduled_family_positions.iter().zip(&scheduled_family) {
        let q=item.term.row.checked_sub(owner*ROWS).expect("C427 family row precedes owner");
        assert!(q<ATTACHED_ROW_OFFSET+SERIALIZER_ROW_BASE+FAMILY_TERMS,
            "C427 family source row outside pinned family");
        let actual=row_plan.layout.place(expected_class,Relation::Header,owner,item.term.clone()).unwrap();
        let mut expected=item.term.clone();
        expected.row=owner*ROWS+if q<393_216{q}else if q<406_406{507_536+q-393_216}
            else{panic!("C427 family source row outside ROW map owner={owner} q={q}")};
        assert_eq!(actual,expected,"C427 source/placed first divergence owner={owner} global_ordinal={} label={} family_ordinal={} source={:?} expected_placed={:?} actual={:?}",
            item.ordinal,origins[item.ordinal].unwrap().label,origins[item.ordinal].unwrap().family_ordinal,
            crate::c425_span_census::tuple(&item.term),crate::c425_span_census::tuple(&expected),
            crate::c425_span_census::tuple(&actual));
        assert!(actual.gate.left>=owner*WIDTH && actual.gate.left<(owner+1)*WIDTH
            && actual.gate.right>=owner*WIDTH && actual.gate.right<(owner+1)*WIDTH,
            "C427 placed family endpoint escaped owner-local WIDTH owner={owner} ordinal={}",item.ordinal);
        assert_eq!(actual,native_placed[*position],
            "C427 actual RowPlan placed first divergence owner={owner} ordinal={}",item.ordinal);
        family_placed.push(actual);
    }
    let records=scheduled_family.iter().zip(&family_placed)
        .map(|(item,placed)|(item.ordinal,item.term.clone(),placed.clone())).collect::<Vec<_>>();
    let (source_digest,placed_digest)=crate::c425_span_census::c427_owner_sha256(owner,&records)
        .unwrap_or_else(|error|panic!("C427 family digest owner={owner}: {error}"));
    let base_family=family_items(&base,origins);
    let work_family=family_items(&work_tree,origins);
    println!("C427 cold owner={owner} class={expected_class:?} active={active:?} family_base_by_label={:?} family_worktree_by_label={:?} family_roster_by_label={:?} family_scheduled_by_label={:?} family_source={} family_after_worktree={} family_after_roster={} family_after_schedule={} family_placed={} worktree_family_drops={} roster_family_drops={} scheduled_family_drops={} source_sha256={source_digest} placed_sha256={placed_digest} first_global_ordinal={} last_global_ordinal={} native_merge=ordered_full_stream_equal rowplan_stage=matched",
        family_counts(&base_family,origins),family_counts(&work_family,origins),
        family_counts(&source_family,origins),family_counts(&scheduled_family,origins),
        base_family.len(),work_family.len(),source_family.len(),scheduled_family.len(),family_placed.len(),
        base_family.len()-work_family.len(),work_family.len()-source_family.len(),source_family.len()-scheduled_family.len(),
        scheduled_family.first().map_or(0,|item|item.ordinal),scheduled_family.last().map_or(0,|item|item.ordinal));
    scheduled_family.iter().zip(family_placed).map(|(item,term)|Tagged{ordinal:item.ordinal,term}).collect()
}

#[test]
fn c427_boolean_padding_four_owner_cold_ledger_and_row_closure() {
    let (canonical,spans,origins)=canonical_family();
    assert_family_ledger(&canonical,&spans,&origins);
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[7;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    let schedule=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&schedule).unwrap();
    for &(owner,expected_class,expected_active) in &C425_OWNERS {
        cold_owner_family_census(owner,expected_class,expected_active,&parent,&roster,&row_plan,
            &canonical,&spans,&origins);
    }
}

fn c427_packet_bit(packet:&[u8],bit:usize)->bool {
    packet.get(bit/8).is_some_and(|byte|((byte>>(bit%8))&1)!=0)
}

fn c427_set_packet_bit(packet:&mut [u8],bit:usize,value:bool) {
    let byte=packet.get_mut(bit/8).expect("C427 packet bit bounds");
    let mask=1u8<<(bit%8);
    if value {*byte|=mask;}else{*byte&=!mask;}
}

fn c427_hex32(value:&str)->[u8;32] {
    let raw=value.as_bytes();assert_eq!(raw.len(),64);
    let mut out=[0u8;32];
    for (i,pair) in raw.chunks_exact(2).enumerate() {
        let digit=|v:u8|match v {b'0'..=b'9'=>v-b'0',b'A'..=b'F'=>v-b'A'+10,_=>panic!("C427 invalid pinned hex")};
        out[i]=(digit(pair[0])<<4)|digit(pair[1]);
    }
    out
}

fn c427_packet_fixture()->(Vec<Vec<u8>>,Vec<u8>) {
    let owners=[843_776usize,845_759,1_048_576,1_827_840];
    let expected=[
        "85C8467750F8CF0C7CBC84364952D4E8A234BB16F737C6D1BD1C7CA200BBE02A",
        "14378C692B8790DCF97E99E3A5D62A29C511F5936F118626877C3707524117A0",
        "ECEDD2FBC64A41F944F5740496B449FACB24853F1CD6DD305BE52F722A1B1644",
        "4DC9836CB94EF8661496CE07AC00F8ED635A343BD102F23C8006BEF76D6B42A4",
    ];
    let pairs=[(63usize,64usize),(4095,4096),(65_534,65_535),(69_678,69_679)];
    let mut packets=Vec::with_capacity(4);let mut bundle=b"C427-X-PACKETS-v1\0".to_vec();
    for (rank,&owner) in owners.iter().enumerate() {
        let mut packet=(0..131_072usize).map(|k|((37*k+19*(k/251)+53*rank)%256) as u8).collect::<Vec<_>>();
        packet[74_246..81_920].fill(0);
        c427_set_packet_bit(&mut packet,0,owner&1!=0);
        c427_set_packet_bit(&mut packet,1<<19,(owner&1)==0);
        for (bit,value) in [(7,true),(8,true),(1,false),(9,false),(1024,true),(1025,false),
            (32767,true),(50000,true),(50001,false)] {c427_set_packet_bit(&mut packet,(1<<19)+bit,value);}
        for &(a,b) in &pairs {
            let (av,bv)=match rank {0=>(false,false),1=>(false,true),2=>(true,false),_ =>(true,true)};
            c427_set_packet_bit(&mut packet,(1<<19)+a,av);
            c427_set_packet_bit(&mut packet,(1<<19)+b,bv);
        }
        c427_set_packet_bit(&mut packet,(1<<19)+131_072,true);
        assert!(packet[74_246..81_920].iter().all(|byte|*byte==0),"C427 padding nonzero owner={owner}");
        assert!(c427_packet_bit(&packet,(1<<19)+131_072),"C427 sentinel zero owner={owner}");
        let digest=crate::native_prefix_auth_plan::role0_sha256(&packet).unwrap();
        assert_eq!(digest,c427_hex32(expected[rank]),"C427 packet digest owner={owner}");
        bundle.extend_from_slice(&(owner as u64).to_le_bytes());
        bundle.extend_from_slice(&(packet.len() as u64).to_le_bytes());bundle.extend_from_slice(&packet);
        packets.push(packet);
    }
    let bundle_digest=crate::native_prefix_auth_plan::role0_sha256(&bundle).unwrap();
    assert_eq!(bundle_digest,c427_hex32("9FB01DB391141142AE464981249CD2E1FA3DC66BA0C145C963B7ED8981C969DD"));
    (packets,bundle_digest.to_vec())
}

fn c427_binding_payload(bundle_digest:&[u8])->Vec<u8> {
    let statement=b"C427 source-owned Boolean-padding family; four C220 owners; k1; family-only synthetic differential";
    let pins=[
        "AF9C09C5D2DDCF283441D3621BA3EAD6DCF42C440121326EACEC76A27B691623",
        "50B0A3A03482F58B02AE37C1C9710E40986C014A2ECD5597248E34CF5D52CC9A",
        "4F74DB124431BDF5AC425A8D7BDE1B5C5CE5A7E29EDF174A34C3C09D80759E2D",
        "DF4A9002BA9A1AB02A62F8A2A8796ADA65CB29BF3F049813A82F6F2D27EF924A",
        "EB764570FFCEC6D8A4EA11F64C80180DE5832651C5722A76C43874A25ABE09A3",
        "63016218A021A692639A63407A9DB38777604AB5EBEEBFED42F61C31DCF1A4C7",
        "91EA77B9CB25DD6CC2D268CC21BB37423119E0ED40E928E7BEFC51A25F4A19B1",
    ];
    let mut payload=statement.to_vec();payload.push(0);
    for pin in pins {payload.extend_from_slice(&c427_hex32(pin));}
    for value in [1_827_840u64,21,1_048_576,524_288,1,69_680,131_072] {payload.extend_from_slice(&value.to_le_bytes());}
    payload.extend_from_slice(b"Scheduled::eligible08()\0");
    for owner in [843_776u64,845_759,1_048_576,1_827_840] {payload.extend_from_slice(&owner.to_le_bytes());}
    payload.extend_from_slice(bundle_digest);assert_eq!(payload.len(),467);
    assert_eq!(crate::native_prefix_auth_plan::role0_sha256(&payload).unwrap(),
        c427_hex32("D48E81B7619BDBEFA741AA9F4E98E7BBE155679BDBDF2729E007D4FE107F9C87"));
    payload
}

fn c427_fr_bytes(value:&Fr)->[u8;32] {
    let mut out=[0u8;32];let raw=value.into_bigint().to_bytes_le();
    assert!(raw.len()<=out.len());out[..raw.len()].copy_from_slice(&raw);out
}

fn c427_hex(bytes:&[u8])->String {
    const HEX:&[u8;16]=b"0123456789ABCDEF";
    let mut out=String::with_capacity(bytes.len()*2);
    for byte in bytes {out.push(HEX[(byte>>4) as usize] as char);out.push(HEX[(byte&15) as usize] as char);}
    out
}

fn c427_prefix_diagnostic() -> (Vec<Vec<u8>>,Vec<Fr>,Fr,Vec<Fr>,Fr,crate::transcript::Transcript) {
    let (packets,bundle_digest)=c427_packet_fixture();
    let payload=c427_binding_payload(&bundle_digest);
    let (canonical,spans,origins)=canonical_family();assert_family_ledger(&canonical,&spans,&origins);
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[7;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();let schedule=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&schedule).unwrap();
    let mut transcript=crate::transcript::Transcript::new(b"C427-H21-HEADER-U-k1-v1\0");
    transcript.append_bytes(b"c427-fixture-binding-v1",&payload);
    let point=crate::gkr::output_point(1usize<<40,&mut transcript);assert_eq!(point.len(),40);
    let local_weights=crate::gkr::eq_weights(&point[..19]);
    let owner_weights=crate::gkr::eq_weights(&point[19..]);
    let mut p0=vec![Fr::zero();3];let mut claim=Fr::zero();let mut kept=0usize;
    for (owner_index,&(owner,expected_class,expected_active)) in C425_OWNERS.iter().enumerate() {
        assert_eq!(roster.owner_class(owner as u64).unwrap(),expected_class);
        let active=source_active_mask(&schedule,owner).unwrap();assert_eq!(active,expected_active);
        let mut rostered=Vec::new();
        roster.visit_header_terms(owner as u64,|term|{
            let ordinal=crate::c425_span_census::current_source_ordinal().ok_or("C427 prefix roster lost ordinal")?;
            rostered.push(Tagged{ordinal,term});Ok(())
        }).unwrap();
        validate_tagged(owner,&canonical,&spans,&rostered,"C427 prefix roster").unwrap();
        let (scheduled,retired)=scheduled_filter(owner,active,&rostered).unwrap();
        assert_eq!(retired,row_plan.header.header_terms(owner).unwrap().retired);
        let native=row_plan.header.header_terms(owner).unwrap();
        compare_terms(&scheduled.iter().map(|item|item.term.clone()).collect::<Vec<_>>(),
            &native.terms,Some(&scheduled.iter().map(|item|item.ordinal).collect::<Vec<_>>()),Some(&spans),
            "C427 prefix candidate/native Merge");
        let mut a=vec![Fr::zero();WIDTH];let mut b=vec![Fr::zero();WIDTH];
        let packet=&packets[owner_index];let rho=owner_weights[owner];let mut owner_kept=0usize;
        for item in family_items(&scheduled,&origins) {
            let placed=row_plan.layout.place(expected_class,Relation::Header,owner,item.term.clone()).unwrap();
            let q=placed.row-owner*ROWS;let l=placed.gate.left-owner*WIDTH;let d=item.term.gate.right-owner*WIDTH;
            let z=if c427_packet_bit(packet,d){Fr::one()}else{Fr::zero()};
            let scale=rho*local_weights[q];
            a[l]+=scale*(item.term.gate.c1+item.term.gate.c3*z);
            b[l]+=scale*(item.term.gate.c0+item.term.gate.c2*z);
            owner_kept+=1;
        }
        assert!(owner_kept>0,"C427 family unexpectedly absent owner={owner}");
        let x=(0..WIDTH).map(|index|if c427_packet_bit(packet,index){Fr::one()}else{Fr::zero()}).collect::<Vec<_>>();
        claim+=a.iter().zip(&b).zip(&x).map(|((av,bv),xv)|*av**xv+*bv).sum::<Fr>();
        for (sum,value) in p0.iter_mut().zip(crate::gkr::quadratic_message(&a,&b,&x)){*sum+=value;}
        kept+=owner_kept;
    }
    assert_eq!(p0[0]+p0.iter().copied().sum::<Fr>(),claim,"C427 literal family p0(0)+p0(1) identity");
    let mut p0_bytes=Vec::new();for value in &p0 {p0_bytes.extend_from_slice(&c427_fr_bytes(value));}
    let p0_digest=crate::native_prefix_auth_plan::role0_sha256(&p0_bytes).unwrap();
    assert_eq!(p0_digest,c427_hex32("414BA2EF6B0E2D7113F894BCC1D1E487D144F1F182D23FAE776DD7A4BCE3DF0B"),
        "C427 frozen literal family p0 digest");
    let claim_bytes=c427_fr_bytes(&claim);
    assert_eq!(claim_bytes,[0u8;32],"C427 frozen literal family claim");
    crate::gkr::append_polynomial(&mut transcript,b"gkr-sumcheck-polynomial",&p0);
    let alpha=transcript.challenge_scalar(b"gkr-sumcheck-challenge");
    assert_ne!(alpha,Fr::zero(),"C427 alpha zero");assert_ne!(alpha,Fr::one(),"C427 alpha one");
    let mut row_alpha=b"C427-K1-ROW-ALPHA-v1\0".to_vec();
    for value in point.iter().chain(std::iter::once(&alpha)){row_alpha.extend_from_slice(&c427_fr_bytes(value));}
    let row_alpha_digest=crate::native_prefix_auth_plan::role0_sha256(&row_alpha).unwrap();
    assert_eq!(row_alpha_digest,c427_hex32("50BEFCA43CEA35E56703C3C20A482DCDE88B790FA9B2569D2794C0243B9099DB"),
        "C427 frozen point/alpha digest");
    let before_clone=(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed());
    assert_eq!(before_clone,(41,51,4_402),"C427 frozen transcript counters after alpha");
    let mut oracle=transcript.clone();let mut candidate=transcript.clone();
    let continuation=[Fr::from(2u64),Fr::from(3u64),Fr::from(5u64)];
    crate::gkr::append_polynomial(&mut oracle,b"gkr-sumcheck-polynomial",&continuation);
    crate::gkr::append_polynomial(&mut candidate,b"gkr-sumcheck-polynomial",&continuation);
    let oracle_next=oracle.challenge_scalar(b"gkr-sumcheck-challenge");
    let candidate_next=candidate.challenge_scalar(b"gkr-sumcheck-challenge");
    assert_eq!(oracle_next,candidate_next);assert_eq!(oracle.challenges(),candidate.challenges());
    assert_eq!(oracle.raw_queries(),candidate.raw_queries());assert_eq!(oracle.bytes_absorbed(),candidate.bytes_absorbed());
    let mut next_bytes=Vec::new();next_bytes.extend_from_slice(&c427_fr_bytes(&oracle_next));
    let next_digest=crate::native_prefix_auth_plan::role0_sha256(&next_bytes).unwrap();
    assert_eq!(next_digest,c427_hex32("8F2053A437065314B0EB011887F080F1E6FAD82598929BE1C4A7A67EC1FAF5A9"),
        "C427 frozen diagnostic continuation digest");
    assert_eq!((oracle.challenges(),oracle.raw_queries(),oracle.bytes_absorbed()),(42,52,4_762),
        "C427 frozen diagnostic continuation counters");
    println!("C427 diagnostic prefix payload_bytes={} payload_sha256={} packet_bundle_sha256={} family_occurrences={kept} p0_sha256={} claim_fr_le={} point_alpha_sha256={} alpha_fr_le={} transcript_before_clone={before_clone:?} continuation_next_sha256={} continuation_counters={:?}",
        payload.len(),"D48E81B7619BDBEFA741AA9F4E98E7BBE155679BDBDF2729E007D4FE107F9C87",
        "9FB01DB391141142AE464981249CD2E1FA3DC66BA0C145C963B7ED8981C969DD",
        c427_hex(&p0_digest),c427_hex(&claim_bytes),c427_hex(&row_alpha_digest),c427_hex(&c427_fr_bytes(&alpha)),c427_hex(&next_digest),
        (oracle.challenges(),oracle.raw_queries(),oracle.bytes_absorbed()));
    (packets,point,alpha,p0,claim,transcript)
}

#[test]
fn c427_k1_family_prefix_packet_binding_and_cold_p0() {
    let _ = c427_prefix_diagnostic();
}

// Diagnostic Boolean-family candidate only. These fixed-size arrays are
// prepared after alpha; owner evaluation never receives a source term list.
const C427_BOOLEAN_BYTE_START:usize=SERIALIZER_WIRE_BASE/8;
const C427_BOOLEAN_BYTES:usize=BOOLEAN_TERMS/8;
const C427_PADDING_BYTE_START:usize=(SERIALIZER_WIRE_BASE+BOOLEAN_TERMS)/8;
const C427_PADDING_BYTE_END:usize=(SERIALIZER_WIRE_BASE+FAMILY_TERMS)/8;
const C427_BOOLEAN_ROW_START:usize=ATTACHED_ROW_OFFSET+SERIALIZER_ROW_BASE;
const C427_HIGH_FIRST:usize=C427_BOOLEAN_ROW_START/64;
const C427_HIGH_COUNT:usize=(C427_BOOLEAN_ROW_START+BOOLEAN_TERMS-1)/64-C427_HIGH_FIRST+1;

#[derive(Default,Debug)]
struct C427ByteOps {
    packet_byte_reads:u64,
    boolean_byte_reads:u64,
    padding_byte_reads:u64,
    sentinel_byte_reads:u64,
    lut_index_events:u64,
    lut_field_reads:u64,
    high_setup_reads:u64,
    high_byte_reads:u64,
    mid_byte_reads:u64,
    table_bit_tests:u64,
    fr_from_bits:u64,
    fr_adds:u64,
    fr_subs:u64,
    fr_muls:u64,
}

impl C427ByteOps {
    fn field_ops(&self)->u64 { self.fr_adds+self.fr_subs+self.fr_muls }
}

fn c427_byte_add(ops:&mut C427ByteOps,a:Fr,b:Fr)->Fr {ops.fr_adds+=1;a+b}
fn c427_byte_sub(ops:&mut C427ByteOps,a:Fr,b:Fr)->Fr {ops.fr_subs+=1;a-b}
fn c427_byte_mul(ops:&mut C427ByteOps,a:Fr,b:Fr)->Fr {ops.fr_muls+=1;a*b}

fn c427_byte_eq_index(point:&[Fr],index:usize,ops:&mut C427ByteOps)->Fr {
    assert!(point.len()<usize::BITS as usize && index<(1usize<<point.len()));
    let mut value=Fr::one();
    for (bit,&coordinate) in point.iter().enumerate() {
        let factor=if (index>>bit)&1==1 {coordinate}
            else {c427_byte_sub(ops,Fr::one(),coordinate)};
        value=c427_byte_mul(ops,value,factor);
    }
    value
}

// Channel 0 is c1=-1; channel 1 is c3=+1 times the original right bit.
// Table key is only the packet byte, independent of owner and source ordinal.
fn c427_build_boolean_byte_lut(
    low_row:&[Fr;3],alpha:Fr,ops:&mut C427ByteOps
)->[[[Fr;3];2];256] {
    let chi=[c427_byte_sub(ops,Fr::one(),alpha),alpha];
    let mut low_eq=[Fr::zero();8];
    for (b,value) in low_eq.iter_mut().enumerate() {
        *value=c427_byte_eq_index(low_row,b,ops);
    }
    let mut table=[[[Fr::zero();3];2];256];
    for raw in 0..256usize {
        let mut x=[Fr::zero();8];
        for (b,value) in x.iter_mut().enumerate() {
            ops.table_bit_tests+=1;
            ops.fr_from_bits+=1;
            *value=Fr::from(((raw>>b)&1) as u64);
        }
        let mut folded_x=[Fr::zero();4];
        for pair in 0..4 {
            let delta=c427_byte_sub(ops,x[2*pair+1],x[2*pair]);
            let scaled=c427_byte_mul(ops,alpha,delta);
            folded_x[pair]=c427_byte_add(ops,x[2*pair],scaled);
        }
        let dy=[
            c427_byte_sub(ops,folded_x[1],folded_x[0]),
            c427_byte_sub(ops,folded_x[3],folded_x[2]),
        ];
        for b in 0..8 {
            let nibble=b/4;
            let y0=folded_x[2*nibble];
            let delta=dy[nibble];
            let basis=if (b>>1)&1==0 {
                [y0,c427_byte_sub(ops,delta,y0),c427_byte_sub(ops,Fr::zero(),delta)]
            } else {[Fr::zero(),y0,delta]};
            let weight=c427_byte_mul(ops,low_eq[b],chi[b&1]);
            for coefficient in 0..3 {
                let scaled=c427_byte_mul(ops,weight,basis[coefficient]);
                let c1=c427_byte_sub(ops,Fr::zero(),scaled);
                table[raw][0][coefficient]=
                    c427_byte_add(ops,table[raw][0][coefficient],c1);
                let c3=c427_byte_mul(ops,scaled,x[b]);
                table[raw][1][coefficient]=
                    c427_byte_add(ops,table[raw][1][coefficient],c3);
            }
        }
    }
    table
}

struct C427BooleanBytePrepared {
    lut:[[[Fr;3];2];256],
    high_eq:[Fr;C427_HIGH_COUNT],
    mid_eq:[Fr;8],
}

impl C427BooleanBytePrepared {
    fn new(point:&[Fr],alpha:Fr,setup:&mut C427ByteOps)->Self {
        assert_eq!(point.len(),40);
        assert_eq!(C427_BOOLEAN_BYTE_START,65_536);
        assert_eq!(C427_BOOLEAN_BYTES,8_710);
        assert_eq!(C427_PADDING_BYTE_START,74_246);
        assert_eq!(C427_PADDING_BYTE_END,81_920);
        assert_eq!(C427_BOOLEAN_ROW_START,35_592);
        assert_eq!(C427_BOOLEAN_ROW_START%64,8);
        assert_eq!(C427_HIGH_FIRST,556);
        assert_eq!(C427_HIGH_COUNT,1_089);
        let low_row=[point[0],point[1],point[2]];
        let lut=c427_build_boolean_byte_lut(&low_row,alpha,setup);
        let mut high_eq=[Fr::zero();C427_HIGH_COUNT];
        for (offset,value) in high_eq.iter_mut().enumerate() {
            *value=c427_byte_eq_index(&point[6..19],C427_HIGH_FIRST+offset,setup);
        }
        let mut mid_eq=[Fr::zero();8];
        for (t,value) in mid_eq.iter_mut().enumerate() {
            *value=c427_byte_eq_index(&point[3..6],t,setup);
        }
        Self {lut,high_eq,mid_eq}
    }
}

struct C427BooleanOwnerScratch {
    rho_high:[Fr;C427_HIGH_COUNT],
    channels:[[Fr;3];2],
    combined:[Fr;3],
}

fn c427_boolean_byte_owner(
    prepared:&C427BooleanBytePrepared,point:&[Fr],owner:usize,packet:&[u8],
    ops:&mut C427ByteOps
)->([[Fr;3];2],[Fr;3],usize) {
    assert_eq!(point.len(),40);
    assert!(owner<(1usize<<21));
    assert_eq!(packet.len(),WIDTH/8);
    let mut scratch=C427BooleanOwnerScratch {
        rho_high:[Fr::zero();C427_HIGH_COUNT],
        channels:[[Fr::zero();3];2],
        combined:[Fr::zero();3],
    };
    // This is an explicit fixed-buffer size, not a process-peak claim.
    // The point and packet are borrowed; no X or source-term array is owned.
    let explicit_owned_bytes=std::mem::size_of_val(prepared)+std::mem::size_of_val(&scratch);
    for &byte in &packet[C427_PADDING_BYTE_START..C427_PADDING_BYTE_END] {
        ops.packet_byte_reads+=1;
        ops.padding_byte_reads+=1;
        assert_eq!(byte,0,"C427 owner packet padding byte is nonzero");
    }
    let sentinel=packet[C427_PADDING_BYTE_END];
    ops.packet_byte_reads+=1;
    ops.sentinel_byte_reads+=1;
    assert_ne!(sentinel&1,0,"C427 post-padding sentinel bit is zero");
    let rho=c427_byte_eq_index(&point[19..40],owner,ops);
    for (offset,value) in scratch.rho_high.iter_mut().enumerate() {
        ops.high_setup_reads+=1;
        *value=c427_byte_mul(ops,rho,prepared.high_eq[offset]);
    }
    // q=35592+8*k+b. Every byte's eight rows remain in one 64-row block.
    for k in 0..C427_BOOLEAN_BYTES {
        let byte=packet[C427_BOOLEAN_BYTE_START+k];
        ops.packet_byte_reads+=1;
        ops.boolean_byte_reads+=1;
        let q_byte=C427_BOOLEAN_ROW_START/8+k;
        let high=(q_byte/8)-C427_HIGH_FIRST;
        let mid=q_byte&7;
        let channels=&prepared.lut[byte as usize];
        ops.lut_index_events+=1;
        let rho_high=scratch.rho_high[high];
        ops.high_byte_reads+=1;
        let mid_eq=prepared.mid_eq[mid];
        ops.mid_byte_reads+=1;
        let scale=c427_byte_mul(ops,rho_high,mid_eq);
        for channel in 0..2 {
            for coefficient in 0..3 {
                ops.lut_field_reads+=1;
                let product=c427_byte_mul(ops,scale,channels[channel][coefficient]);
                scratch.channels[channel][coefficient]=
                    c427_byte_add(ops,scratch.channels[channel][coefficient],product);
            }
        }
    }
    for coefficient in 0..3 {
        scratch.combined[coefficient]=c427_byte_add(
            ops,scratch.channels[0][coefficient],scratch.channels[1][coefficient]);
    }
    (scratch.channels,scratch.combined,explicit_owned_bytes)
}

// Test-only grammar expansion. Its inputs deliberately exclude canonical
// terms, source ordinals, origins, row plans, and cold-oracle vectors.
fn c427_expand_family_grammar(point:&[Fr],owner:usize,packet:&[u8])->(Vec<Fr>,Vec<Fr>) {
    assert_eq!(point.len(),40);assert_eq!(packet.len(),WIDTH/8);
    let local=crate::gkr::eq_weights(&point[..19]);
    let mut rho=Fr::one();
    for (bit,&coordinate) in point[19..].iter().enumerate() {
        rho*=if (owner>>bit)&1==1 {coordinate}else{Fr::one()-coordinate};
    }
    let mut a=vec![Fr::zero();WIDTH];let b=vec![Fr::zero();WIDTH];
    for family_index in 0..FAMILY_TERMS {
        let q=C427_BOOLEAN_ROW_START+family_index;
        let right=if family_index<BOOLEAN_TERMS {SERIALIZER_WIRE_BASE+family_index}else{SERIALIZER_WIRE_BASE};
        let z=if c427_packet_bit(packet,right){Fr::one()}else{Fr::zero()};
        let (c1,c3)=if family_index<BOOLEAN_TERMS {(-Fr::one(),Fr::one())}
            else {(Fr::one(),Fr::zero())};
        a[SERIALIZER_WIRE_BASE+family_index]+=rho*local[q]*(c1+c3*z);
    }
    (a,b)
}

fn c427_assert_fr_vectors(expected:&[Fr],observed:&[Fr],label:&str) {
    assert_eq!(expected.len(),observed.len(),"C427 {label} length mismatch");
    if let Some(index)=(0..expected.len()).find(|&index|expected[index]!=observed[index]) {
        panic!("C427 {label} first divergence index={index} expected={:?} observed={:?}",
            c427_fr_bytes(&expected[index]),c427_fr_bytes(&observed[index]));
    }
}

fn c427_ordinal_coverage(placed:&[Tagged],expected_start:usize)->Result<(),usize> {
    for (offset,item) in placed.iter().enumerate() {
        if item.ordinal!=expected_start+offset {return Err(offset);}
    }
    if placed.len()!=FAMILY_TERMS {return Err(placed.len().min(FAMILY_TERMS));}
    Ok(())
}

fn c427_eq_scalar(point:&[Fr],index:usize)->Fr {
    point.iter().enumerate().fold(Fr::one(),|acc,(bit,&coordinate)|
        acc*if (index>>bit)&1==1 {coordinate}else{Fr::one()-coordinate})
}

fn c427_cold_channel_message(
    point:&[Fr],alpha:Fr,owner:usize,packet:&[u8],placed:&[Tagged],origins:&[Option<crate::c425_span_census::SerializerFamilyOrigin>],channel:usize,
)->[Fr;3] {
    let local=crate::gkr::eq_weights(&point[..19]);
    let mut rho=Fr::one();
    for (bit,&coordinate) in point[19..].iter().enumerate() {
        rho*=if (owner>>bit)&1==1 {coordinate}else{Fr::one()-coordinate};
    }
    let mut a=vec![Fr::zero();WIDTH];let mut b=vec![Fr::zero();WIDTH];
    let mut x=(0..WIDTH).map(|i|if c427_packet_bit(packet,i){Fr::one()}else{Fr::zero()}).collect::<Vec<_>>();
    for item in placed {
        let origin=origins[item.ordinal].expect("C427 cold channel lost family origin");
        let is_boolean=origin.label=="serializer_boolean_diagonal";
        if (channel<2)!=is_boolean {continue;}
        let q=item.term.row-owner*ROWS;let left=item.term.gate.left-owner*WIDTH;
        let right=item.term.gate.right-owner*WIDTH;
        let z=if c427_packet_bit(packet,right){Fr::one()}else{Fr::zero()};
        let (c1,c3)=if channel==0 {(item.term.gate.c1,Fr::zero())}
            else if channel==1 {(Fr::zero(),item.term.gate.c3)}
            else {(item.term.gate.c1,Fr::zero())};
        a[left]+=rho*local[q]*(c1+c3*z);
    }
    if channel==2 {
        assert_eq!(BOOLEAN_TERMS%16,0,"C427 padding must start on a 16-row boundary");
        assert_eq!(FAMILY_TERMS%16,0,"C427 family end must be on a 16-row boundary");
        assert!(packet[C427_PADDING_BYTE_START..C427_PADDING_BYTE_END].iter().all(|byte|*byte==0),
            "C427 padding X interval is not zero");
        for i in BOOLEAN_TERMS..FAMILY_TERMS {
            assert_eq!(x[SERIALIZER_WIRE_BASE+i],Fr::zero(),"C427 padding X bit {}",SERIALIZER_WIRE_BASE+i);
        }
    }
    crate::gkr::fold(&mut a,alpha);crate::gkr::fold(&mut b,alpha);
    crate::gkr::fold(&mut x,alpha);
    let message=crate::gkr::quadratic_message(&a,&b,&x);
    x.clear();[message[0],message[1],message[2]]
}

#[test]
fn c427_boolean_byte_lut_four_owner_frozen_point_differential() {
    let prefix_start=std::time::Instant::now();
    let (packets,point,alpha,expected_p0,expected_claim,transcript_after_alpha)=c427_prefix_diagnostic();
    let prefix_ms=prefix_start.elapsed().as_millis();
    assert_eq!(packets.len(),4);assert_eq!(point.len(),40);
    assert_eq!(c427_fr_bytes(&alpha),c427_hex32("D410C3C1D9450A99D779995AEC1362A4DB11269A451215BEDC6F3546C6633B13"));
    let mut cold_messages=[[[Fr::zero();3];3];4];let mut source_cold_ms=0u128;
    let mut grammar_qualification_ms=0u128;
    let mut grammar_p0=[Fr::zero();3];let mut grammar_claim=Fr::zero();
    let qualification_start=std::time::Instant::now();
    {
        let (canonical,spans,origins)=canonical_family();assert_family_ledger(&canonical,&spans,&origins);
        let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[7;32],[0;28]).unwrap();
        let roster=DaaHistoryRoster::compile(&parent).unwrap();let schedule=Scheduled::eligible08();
        let row_plan=RowPlan::new(&roster,&schedule).unwrap();
        for (owner_index,&(owner,class,active)) in C425_OWNERS.iter().enumerate() {
            let cold_start=std::time::Instant::now();
            let placed=cold_owner_family_census(owner,class,active,&parent,&roster,&row_plan,
                &canonical,&spans,&origins);
            source_cold_ms+=cold_start.elapsed().as_millis();
            assert_eq!(placed.len(),FAMILY_TERMS,"C427 owner={owner} family occurrence count");
            let expected_start=placed.first().expect("C427 family owner empty").ordinal;
            assert_eq!(c427_ordinal_coverage(&placed,expected_start),Ok(()),
                "C427 owner={owner} family ordinal coverage");
            let padding_position=placed.iter().position(|item|
                origins[item.ordinal].is_some_and(|origin|origin.label=="serializer_input_padding"))
                .expect("C427 missing padding source occurrence");
            assert_eq!(padding_position,BOOLEAN_TERMS,"C427 padding origin boundary");
            let mut missing_padding=placed.clone();missing_padding.remove(padding_position);
            assert!(c427_ordinal_coverage(&missing_padding,expected_start).is_err(),
                "C427 missing padding source ordinal mutant accepted");
            let mut duplicated_padding=placed.clone();
            duplicated_padding.insert(padding_position+1,placed[padding_position].clone());
            assert!(c427_ordinal_coverage(&duplicated_padding,expected_start).is_err(),
                "C427 duplicated padding source ordinal mutant accepted");
            for omitted in [0usize,BOOLEAN_TERMS-1] {
                let mut missing_boolean=placed.clone();missing_boolean.remove(omitted);
                assert!(c427_ordinal_coverage(&missing_boolean,expected_start).is_err(),
                    "C427 omitted first/last Boolean occurrence mutant accepted index={omitted}");
            }
            let mut wrong_left=placed.clone();wrong_left[0].term.gate.left+=1;
            assert!(validate_tagged(owner,&canonical,&spans,&wrong_left,"C427 Boolean left-index mutant").is_err(),
                "C427 Boolean left-index mutant accepted");
            let mut wrong_right_boolean=placed.clone();wrong_right_boolean[0].term.gate.right+=1;
            assert!(validate_tagged(owner,&canonical,&spans,&wrong_right_boolean,"C427 Boolean right-index mutant").is_err(),
                "C427 Boolean right-index mutant accepted");
            let mut wrong_row=placed.clone();wrong_row[0].term.row+=1;
            assert!(validate_tagged(owner,&canonical,&spans,&wrong_row,"C427 Boolean row mutant").is_err(),
                "C427 Boolean source-row mutant accepted");
            let boundary_index=64-(C427_BOOLEAN_ROW_START%64);
            assert_eq!((C427_BOOLEAN_ROW_START+boundary_index)%64,0);
            let mut wrong_boundary=placed.clone();wrong_boundary[boundary_index].term.row-=1;
            assert!(validate_tagged(owner,&canonical,&spans,&wrong_boundary,"C427 Boolean 64-row boundary mutant").is_err(),
                "C427 Boolean 64-row boundary mutant accepted");
            let mut wrong_right=placed.clone();wrong_right[padding_position].term.gate.right=owner*WIDTH;
            assert!(validate_tagged(owner,&canonical,&spans,&wrong_right,"C427 padding-global-X0 mutant").is_err(),
                "C427 padding global-X[0] endpoint mutant accepted");
            for (family_index,item) in placed.iter().enumerate() {
                assert_eq!(item.ordinal,placed[0].ordinal+family_index,"C427 owner={owner} family ordinal order");
                let origin=origins[item.ordinal].unwrap();
                assert_eq!(origin.label,if family_index<BOOLEAN_TERMS {"serializer_boolean_diagonal"} else {"serializer_input_padding"},
                    "C427 owner={owner} first family source label divergence at {family_index}");
            }
            let grammar_start=std::time::Instant::now();
            let (mut qualified_a,mut qualified_b)=c427_expand_family_grammar(&point,owner,&packets[owner_index]);
            let mut cold_a=vec![Fr::zero();WIDTH];let mut cold_b=vec![Fr::zero();WIDTH];
            let local=crate::gkr::eq_weights(&point[..19]);let mut rho=Fr::one();
            for (bit,&coordinate) in point[19..].iter().enumerate() {
                rho*=if (owner>>bit)&1==1 {coordinate}else{Fr::one()-coordinate};
            }
            for item in &placed {
                let q=item.term.row-owner*ROWS;let left=item.term.gate.left-owner*WIDTH;
                let right=item.term.gate.right-owner*WIDTH;
                let z=if c427_packet_bit(&packets[owner_index],right){Fr::one()}else{Fr::zero()};
                cold_a[left]+=rho*local[q]*(item.term.gate.c1+item.term.gate.c3*z);
                cold_b[left]+=rho*local[q]*(item.term.gate.c0+item.term.gate.c2*z);
            }
            c427_assert_fr_vectors(&cold_a,&qualified_a,&format!("grammar/cold A owner={owner}"));
            c427_assert_fr_vectors(&cold_b,&qualified_b,&format!("grammar/cold B owner={owner}"));
            let qualification_x=(0..WIDTH).map(|i|if c427_packet_bit(&packets[owner_index],i){Fr::one()}else{Fr::zero()}).collect::<Vec<_>>();
            let owner_p0=crate::gkr::quadratic_message(&qualified_a,&qualified_b,&qualification_x);
            for (sum,value) in grammar_p0.iter_mut().zip(owner_p0) {*sum+=value;}
            grammar_claim+=qualified_a.iter().zip(&qualified_b).zip(&qualification_x)
                .map(|((av,bv),xv)|*av**xv+*bv).sum::<Fr>();
            drop(qualification_x);
            assert!(qualified_a[SERIALIZER_WIRE_BASE+BOOLEAN_TERMS..SERIALIZER_WIRE_BASE+FAMILY_TERMS].iter().any(|v|!v.is_zero()),
                "C427 padding A vector must be present in qualification owner={owner}");
            crate::gkr::fold(&mut qualified_a,alpha);crate::gkr::fold(&mut qualified_b,alpha);
            crate::gkr::fold(&mut cold_a,alpha);crate::gkr::fold(&mut cold_b,alpha);
            c427_assert_fr_vectors(&cold_a,&qualified_a,&format!("post-alpha A-prime owner={owner}"));
            c427_assert_fr_vectors(&cold_b,&qualified_b,&format!("post-alpha B-prime owner={owner}"));
            let mut rho=Fr::one();
            for (bit,&coordinate) in point[19..].iter().enumerate() {
                rho*=if (owner>>bit)&1==1 {coordinate}else{Fr::one()-coordinate};
            }
            let interpolation=(Fr::one()-alpha)*(Fr::one()-point[0])+alpha*point[0];
            for t in [0usize,15_347,30_695] {
                let index=296_984+t;let expected=rho*c427_eq_scalar(&point[1..19],52_636+t)*interpolation;
                assert_eq!(qualified_a[index],expected,"C427 owner={owner} selected padding A-prime index={index}");
                assert!(!qualified_a[index].is_zero(),"C427 owner={owner} selected padding A-prime unexpectedly zero index={index}");
            }
            assert!(qualified_a[296_984..327_680].iter().any(|v|!v.is_zero()),
                "C427 padding A-prime vector must be present owner={owner}");
            assert!(qualified_b.iter().all(|value|value.is_zero()),"C427 family B vector nonzero owner={owner}");
            for channel in 0..3 {
                cold_messages[owner_index][channel]=c427_cold_channel_message(&point,alpha,owner,
                    &packets[owner_index],&placed,&origins,channel);
            }
            // The padding A vector is nonzero, but this post-alpha p1
            // message vanishes: source padding is pair-aligned and X is zero.
            assert_eq!(cold_messages[owner_index][2],[Fr::zero();3],
                "C427 padding channel must be zero after this alpha fold; later U rounds are out of scope owner={owner}");
            grammar_qualification_ms+=grammar_start.elapsed().as_millis();
        }
    }
    let qualification_ms=qualification_start.elapsed().as_millis();
    assert_eq!(grammar_p0.as_slice(),expected_p0.as_slice(),"C427 grammar/cold first-round p0 mismatch");
    assert_eq!(grammar_claim,expected_claim,"C427 grammar/cold claim mismatch");
    assert_eq!(grammar_p0[0]+grammar_p0.iter().copied().sum::<Fr>(),grammar_claim,
        "C427 grammar p0(0)+p0(1) identity");
    let mut setup=C427ByteOps::default();let hot_start=std::time::Instant::now();
    let mut prepared=C427BooleanBytePrepared::new(&point,alpha,&mut setup);
    let mut hot_messages=[[[Fr::zero();3];2];4];let mut total_owned=std::mem::size_of_val(&prepared)
        +std::mem::size_of_val(&hot_messages)+std::mem::size_of::<C427ByteOps>();
    let mut runtime_totals=C427ByteOps::default();let mut owner_zero_channels=None;
    for (owner_index,&(owner,_,_)) in C425_OWNERS.iter().enumerate() {
        let mut ops=C427ByteOps::default();
        let (channels,combined,owned)=c427_boolean_byte_owner(&prepared,&point,owner,
            &packets[owner_index],&mut ops);
        assert_eq!(ops.boolean_byte_reads,8_710);assert_eq!(ops.padding_byte_reads,7_674);
        assert_eq!(ops.sentinel_byte_reads,1);assert_eq!(ops.packet_byte_reads,16_385);
        assert_eq!(ops.lut_index_events,8_710);assert_eq!(ops.lut_field_reads,6*8_710);
        assert_eq!(combined,std::array::from_fn(|i|channels[0][i]+channels[1][i]));
        for channel in 0..2 {
            hot_messages[owner_index][channel]=channels[channel];
            assert_eq!(channels[channel],cold_messages[owner_index][channel],
                "C427 hot/cold c-channel first divergence owner={owner} channel={channel}");
        }
        if owner_index==0 {owner_zero_channels=Some(channels);}
        total_owned=total_owned.saturating_add(owned)
            .saturating_add(std::mem::size_of_val(&channels))
            .saturating_add(std::mem::size_of_val(&combined))
            .saturating_add(std::mem::size_of_val(&ops));
        runtime_totals.packet_byte_reads+=ops.packet_byte_reads;
        runtime_totals.boolean_byte_reads+=ops.boolean_byte_reads;runtime_totals.padding_byte_reads+=ops.padding_byte_reads;
        runtime_totals.sentinel_byte_reads+=ops.sentinel_byte_reads;runtime_totals.lut_index_events+=ops.lut_index_events;
        runtime_totals.lut_field_reads+=ops.lut_field_reads;runtime_totals.high_setup_reads+=ops.high_setup_reads;
        runtime_totals.high_byte_reads+=ops.high_byte_reads;runtime_totals.mid_byte_reads+=ops.mid_byte_reads;
        runtime_totals.table_bit_tests+=ops.table_bit_tests;runtime_totals.fr_from_bits+=ops.fr_from_bits;
        runtime_totals.fr_adds+=ops.fr_adds;
        runtime_totals.fr_subs+=ops.fr_subs;runtime_totals.fr_muls+=ops.fr_muls;
    }
    let hot_ms=hot_start.elapsed().as_millis();
    assert!(hot_ms<=120_000,"C427 hot cap exceeded: {hot_ms} ms");
    assert!(total_owned<=1usize<<30,"C427 hot owned-state cap exceeded: {total_owned}");
    let baseline=owner_zero_channels.expect("C427 missing owner-zero output");
    let first_key=packets[0][C427_BOOLEAN_BYTE_START] as usize;
    let saved=prepared.lut[first_key][0][0];prepared.lut[first_key][0][0]=-saved;
    let mut sign_ops=C427ByteOps::default();
    let (sign_mutant,_,_)=c427_boolean_byte_owner(&prepared,&point,C425_OWNERS[0].0,&packets[0],&mut sign_ops);
    prepared.lut[first_key][0][0]=saved;
    assert_ne!(sign_mutant[0],baseline[0],"C427 isolated c1 sign mutant escaped");
    let mut owner_ops=C427ByteOps::default();
    let (wrong_owner,_,_)=c427_boolean_byte_owner(&prepared,&point,C425_OWNERS[0].0+1,&packets[0],&mut owner_ops);
    assert_ne!(wrong_owner,baseline,"C427 isolated owner-selector mutant escaped");
    for bit in [SERIALIZER_WIRE_BASE,SERIALIZER_WIRE_BASE+BOOLEAN_TERMS-1] {
        let mut changed=packets[0].clone();let was_set=c427_packet_bit(&changed,bit);
        c427_set_packet_bit(&mut changed,bit,!was_set);
        let mut ops=C427ByteOps::default();
        let (observed,_,_)=c427_boolean_byte_owner(&prepared,&point,C425_OWNERS[0].0,&changed,&mut ops);
        assert_ne!(observed,baseline,"C427 first/last used-bit mutant escaped bit={bit}");
    }
    let mut padding_mutant=packets[0].clone();padding_mutant[C427_PADDING_BYTE_START]|=1;
    let rejected=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||{
        let mut ops=C427ByteOps::default();
        c427_boolean_byte_owner(&prepared,&point,C425_OWNERS[0].0,&padding_mutant,&mut ops)
    }));
    assert!(rejected.is_err(),"C427 nonzero padding mutant was accepted");
    let total:[Fr;3]=std::array::from_fn(|coefficient|{
        C425_OWNERS.iter().enumerate().fold(Fr::zero(),|sum,(owner_index,_)|sum+hot_messages[owner_index][0][coefficient]+hot_messages[owner_index][1][coefficient])
    });
    let cold_total:[Fr;3]=std::array::from_fn(|coefficient|{
        C425_OWNERS.iter().enumerate().fold(Fr::zero(),|sum,(owner_index,_)|sum+cold_messages[owner_index][0][coefficient]+cold_messages[owner_index][1][coefficient]+cold_messages[owner_index][2][coefficient])
    });
    assert_eq!(total,cold_total,"C427 four-owner total first divergence");
    let mut oracle=transcript_after_alpha.clone();let mut candidate=transcript_after_alpha;
    crate::gkr::append_polynomial(&mut oracle,b"gkr-sumcheck-polynomial",&cold_total);
    crate::gkr::append_polynomial(&mut candidate,b"gkr-sumcheck-polynomial",&total);
    let oracle_next=oracle.challenge_scalar(b"gkr-sumcheck-challenge");
    let candidate_next=candidate.challenge_scalar(b"gkr-sumcheck-challenge");
    assert_eq!(oracle_next,candidate_next);assert_eq!(oracle.challenges(),candidate.challenges());
    assert_eq!(oracle.raw_queries(),candidate.raw_queries());assert_eq!(oracle.bytes_absorbed(),candidate.bytes_absorbed());
    let mut next_bytes=Vec::new();next_bytes.extend_from_slice(&c427_fr_bytes(&candidate_next));
    let next_digest=crate::native_prefix_auth_plan::role0_sha256(&next_bytes).unwrap();
    println!("C427 four-owner scoped differential PASS owners=4 family_terms_per_owner={FAMILY_TERMS} prefix_cold_p0_ms={prefix_ms} total_qualification_ms={qualification_ms} source_cold_ms={source_cold_ms} grammar_qualification_ms={grammar_qualification_ms} grammar_oracle_vector_state_bytes={} setup_fr_adds={} setup_fr_subs={} setup_fr_muls={} setup_field_ops={} setup_table_bit_tests={} setup_fr_from_bits={} hot_ms={hot_ms} hot_explicit_owned_bytes={total_owned} packet_reads={} boolean_reads={} padding_reads={} sentinel_reads={} lut_indices={} lut_fields={} high_setup={} high_byte={} mid_byte={} table_bit_tests={} fr_from_bits={} fr_adds={} fr_subs={} fr_muls={} source_callbacks=unmeasured grammar_source_callbacks=0 grammar_p0_claim=literal-equal continuation_sha256={} continuation_counters={:?} scope=family-only-p1-not-full-U-or-C220-transcript",
        (5*WIDTH+(1usize<<19))*std::mem::size_of::<Fr>(),setup.fr_adds,setup.fr_subs,setup.fr_muls,setup.field_ops(),setup.table_bit_tests,setup.fr_from_bits,
        runtime_totals.packet_byte_reads,runtime_totals.boolean_byte_reads,runtime_totals.padding_byte_reads,
        runtime_totals.sentinel_byte_reads,runtime_totals.lut_index_events,runtime_totals.lut_field_reads,
        runtime_totals.high_setup_reads,runtime_totals.high_byte_reads,runtime_totals.mid_byte_reads,
        runtime_totals.table_bit_tests,runtime_totals.fr_from_bits,runtime_totals.fr_adds,runtime_totals.fr_subs,runtime_totals.fr_muls,
        c427_hex(&next_digest),(candidate.challenges(),candidate.raw_queries(),candidate.bytes_absorbed()));
}

#[test]
fn c427_boolean_byte_lut_all_256_c397_second_u_microdifferential() {
    let alpha=Fr::from(17u64);
    let low_row=[Fr::from(7u64),Fr::from(11u64),Fr::from(23u64)];
    let mut setup=C427ByteOps::default();
    let table=c427_build_boolean_byte_lut(&low_row,alpha,&mut setup);
    let row_weights=crate::gkr::eq_weights(&low_row);
    for raw in 0..256usize {
        let mut x=vec![Fr::zero();8];
        for (b,value) in x.iter_mut().enumerate() {
            *value=Fr::from(((raw>>b)&1) as u64);
        }
        for channel in 0..2 {
            let mut a=vec![Fr::zero();8];
            let mut b=vec![Fr::zero();8];
            for index in 0..8 {
                a[index]=if channel==0 {-row_weights[index]}
                    else {row_weights[index]*x[index]};
            }
            let mut folded_x=x.clone();
            crate::gkr::fold(&mut a,alpha);
            crate::gkr::fold(&mut b,alpha);
            crate::gkr::fold(&mut folded_x,alpha);
            let direct=crate::gkr::quadratic_message(&a,&b,&folded_x);
            assert_eq!(table[raw][channel],[direct[0],direct[1],direct[2]],
                "C427 Boolean byte LUT/C397 first divergence byte={raw} channel={channel}");
        }
    }
    assert_eq!(setup.table_bit_tests,256*8);
    assert_eq!(setup.fr_from_bits,256*8);
    assert_eq!(setup.packet_byte_reads,0);
    assert_eq!(setup.lut_index_events,0);
    println!("C427 Boolean byte LUT micro PASS: bytes=256 channels=2 coefficients=3 alpha=17 r_low3=[7,11,23] setup_fr_ops={} setup_bit_tests={}",
        setup.field_ops(),setup.table_bit_tests);
}

#[test]
fn c427_boolean_byte_lut_one_owner_scan_cost_and_padding() {
    let point=(0..40usize).map(|i|Fr::from((2*i+3) as u64)).collect::<Vec<_>>();
    let alpha=Fr::from(17u64);
    let mut setup=C427ByteOps::default();
    let prepared=C427BooleanBytePrepared::new(&point,alpha,&mut setup);
    let (packets,_bundle)=c427_packet_fixture();
    let owner=843_776usize;
    let mut runtime=C427ByteOps::default();
    let (channels,combined,owned_bytes)=
        c427_boolean_byte_owner(&prepared,&point,owner,&packets[0],&mut runtime);
    assert_eq!(runtime.boolean_byte_reads,8_710);
    assert_eq!(runtime.padding_byte_reads,7_674);
    assert_eq!(runtime.sentinel_byte_reads,1);
    assert_eq!(runtime.packet_byte_reads,16_385);
    assert_eq!(runtime.lut_index_events,8_710);
    assert_eq!(runtime.lut_field_reads,6*8_710);
    assert_eq!(runtime.high_setup_reads,1_089);
    assert_eq!(runtime.high_byte_reads,8_710);
    assert_eq!(runtime.mid_byte_reads,8_710);
    assert_eq!(runtime.fr_muls,21+1_089+7*8_710);
    assert_eq!(runtime.fr_adds,6*8_710+3);
    assert_eq!(runtime.fr_subs,21-owner.count_ones() as u64);
    assert_eq!(owned_bytes,
        std::mem::size_of::<C427BooleanBytePrepared>()+
        std::mem::size_of::<C427BooleanOwnerScratch>());
    for coefficient in 0..3 {
        assert_eq!(combined[coefficient],
            channels[0][coefficient]+channels[1][coefficient]);
    }
    println!("C427 Boolean byte owner diagnostic: packet_byte_reads={} Boolean_byte_reads={} padding_byte_reads={} sentinel_byte_reads={} LUT_indices={} LUT_field_reads={} high_setup_reads={} high_byte_reads={} mid_byte_reads={} setup_bit_tests={} setup_fr_ops={} owner_fr_ops={} owner_adds={} owner_subs={} owner_muls={} explicit_fixed_state_bytes={} borrowed_packet=true",
        runtime.packet_byte_reads,runtime.boolean_byte_reads,runtime.padding_byte_reads,
        runtime.sentinel_byte_reads,runtime.lut_index_events,runtime.lut_field_reads,
        runtime.high_setup_reads,runtime.high_byte_reads,runtime.mid_byte_reads,
        setup.table_bit_tests,setup.field_ops(),runtime.field_ops(),
        runtime.fr_adds,runtime.fr_subs,runtime.fr_muls,owned_bytes);
}

#[derive(Default,Debug)]
struct C429OneOwnerByteStats {
    packet_byte_reads:u64,
    boolean_family_byte_reads:u64,
    padding_byte_reads:u64,
    sentinel_checks:u64,
    x_lut_lookups:u64,
    x_cell_writes:u64,
    active_a_cell_writes:u64,
    explicit_builder_bytes:usize,
}

const C429_ALL_ROUND_PRECODE_SHA256:&str="4955955D7EA2F8E7846E0F1CDB1235E5A8FBEC7790B6D747BAA1A399ABBA554C";

// Build the post-alpha state from packet bytes only. This function deliberately
// takes no source terms, origins, ordinals, row plan, or cold-oracle vectors.
fn c429_one_owner_byte_state(
    point:&[Fr],alpha:Fr,owner:usize,packet:&[u8]
)->(Vec<Fr>,Vec<Fr>,C429OneOwnerByteStats) {
    assert_eq!(point.len(),40);
    assert_eq!(packet.len(),WIDTH/8);
    let chi=[Fr::one()-alpha,alpha];
    let low_eq=(0..8usize).map(|b|c427_eq_scalar(&point[..3],b)).collect::<Vec<_>>();
    let mut t_bool=vec![[Fr::zero();4];256];
    let mut t_x=vec![[Fr::zero();4];256];
    for raw in 0..256usize {
        for h in 0..4usize {
            let mut bool_value=Fr::zero();
            for offset in 0..2usize {
                let b=2*h+offset;
                let bit=Fr::from(((raw>>b)&1) as u64);
                bool_value+=chi[offset]*low_eq[b]*(bit-Fr::one());
            }
            let low=Fr::from(((raw>>(2*h))&1) as u64);
            let high=Fr::from(((raw>>(2*h+1))&1) as u64);
            t_bool[raw][h]=bool_value;
            t_x[raw][h]=low+alpha*(high-low);
        }
    }
    let t_pad=std::array::from_fn(|h|{
        (0..2usize).map(|offset|{
            let b=2*h+offset;chi[offset]*low_eq[b]
        }).sum::<Fr>()
    });
    let high_eq=crate::gkr::eq_weights(&point[6..19]);
    let mid_eq=crate::gkr::eq_weights(&point[3..6]);
    let rho=c427_eq_scalar(&point[19..],owner);
    let mut a_prime=vec![Fr::zero();WIDTH/2];
    let mut x_prime=vec![Fr::zero();WIDTH/2];
    let mut stats=C429OneOwnerByteStats::default();

    for global_byte in 0..WIDTH/8 {
        let byte=packet[global_byte];
        stats.packet_byte_reads+=1;
        stats.x_lut_lookups+=1;
        for h in 0..4usize {
            x_prime[4*global_byte+h]=t_x[byte as usize][h];
            stats.x_cell_writes+=1;
        }
        if (C427_BOOLEAN_BYTE_START..C427_PADDING_BYTE_END).contains(&global_byte) {
            let family_k=global_byte-C427_BOOLEAN_BYTE_START;
            let q_byte=C427_BOOLEAN_ROW_START/8+family_k;
            let row_factor=mid_eq[q_byte&7]*high_eq[q_byte>>3];
            let family_values=if family_k<BOOLEAN_TERMS/8 {
                stats.boolean_family_byte_reads+=1;
                &t_bool[byte as usize]
            } else {
                stats.padding_byte_reads+=1;
                assert_eq!(byte,0,"C429 one-owner nonzero serializer padding byte={global_byte}");
                &t_pad
            };
            for h in 0..4usize {
                a_prime[262_144+4*family_k+h]=rho*row_factor*family_values[h];
                stats.active_a_cell_writes+=1;
            }
        }
        if global_byte==C427_PADDING_BYTE_END {
            stats.sentinel_checks+=1;
            assert_ne!(byte&1,0,"C429 one-owner post-padding sentinel bit is zero");
        }
    }
    assert_eq!(stats.packet_byte_reads,131_072);
    assert_eq!(stats.boolean_family_byte_reads,8_710);
    assert_eq!(stats.padding_byte_reads,7_674);
    assert_eq!(stats.sentinel_checks,1);
    assert_eq!(stats.x_lut_lookups,131_072);
    assert_eq!(stats.x_cell_writes,524_288);
    assert_eq!(stats.active_a_cell_writes,65_536);
    assert!(a_prime[..262_144].iter().all(|value|value.is_zero()));
    assert!(a_prime[327_680..].iter().all(|value|value.is_zero()));
    assert!(a_prime[262_144..327_680].iter().any(|value|!value.is_zero()));
    stats.explicit_builder_bytes=
        (a_prime.capacity()+x_prime.capacity())*std::mem::size_of::<Fr>()+
        (t_bool.capacity()+t_x.capacity())*std::mem::size_of::<[Fr;4]>()+
        std::mem::size_of_val(&t_pad)+
        (high_eq.capacity()+mid_eq.capacity()+low_eq.capacity())*std::mem::size_of::<Fr>();
    (a_prime,x_prime,stats)
}

// This is intentionally an owner-slice diagnostic: it forks the frozen
// four-owner p0/alpha prefix, then continues with this owner's claim_1 and
// messages. It does not represent the shared four-owner transcript recurrence.
#[test]
fn c429_one_owner_synthetic_all_round_cold_hot_differential() {
    let (packets,point,alpha,_aggregate_p0,claim_0,prefix_after_alpha)=c427_prefix_diagnostic();
    assert_eq!(claim_0,Fr::zero(),"C429 claim_0 must follow Boolean identity and zero padding coverage");
    let owner_index=0usize;
    let (owner,class,active)=C425_OWNERS[owner_index];
    let packet=&packets[owner_index];
    assert_eq!(owner,843_776);
    assert_eq!(packet.len(),131_072);

    let (canonical,spans,origins)=canonical_family();
    assert_family_ledger(&canonical,&spans,&origins);
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[7;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    let schedule=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&schedule).unwrap();
    let placed=cold_owner_family_census(owner,class,active,&parent,&roster,&row_plan,
        &canonical,&spans,&origins);
    assert_eq!(placed.len(),FAMILY_TERMS);
    assert_eq!(c427_ordinal_coverage(&placed,placed[0].ordinal),Ok(()));
    assert_eq!(origins[placed[0].ordinal].unwrap().label,"serializer_boolean_diagonal");
    assert_eq!(origins[placed[BOOLEAN_TERMS].ordinal].unwrap().label,"serializer_input_padding");

    let local_weights=crate::gkr::eq_weights(&point[..19]);
    let rho=c427_eq_scalar(&point[19..],owner);
    let mut cold_a=vec![Fr::zero();WIDTH];
    let mut cold_b=vec![Fr::zero();WIDTH];
    let mut verified_zero_family_terms=0usize;
    for item in &placed {
        let q=item.term.row-owner*ROWS;
        let left=item.term.gate.left-owner*WIDTH;
        let right=item.term.gate.right-owner*WIDTH;
        let right_bit=if c427_packet_bit(packet,right){Fr::one()}else{Fr::zero()};
        let origin=origins[item.ordinal].expect("C429 placed family source label");
        let weighted_a=rho*local_weights[q]*(item.term.gate.c1+item.term.gate.c3*right_bit);
        assert_eq!((item.term.gate.c0,item.term.gate.c2),(Fr::zero(),Fr::zero()),
            "C429 family B polynomial tuple changed ordinal={}",item.ordinal);
        let weighted_b=rho*local_weights[q]*(item.term.gate.c0+item.term.gate.c2*right_bit);
        assert_eq!(weighted_b,Fr::zero(),
            "C429 source-derived B contribution nonzero ordinal={}",item.ordinal);
        let left_bit=if c427_packet_bit(packet,left){Fr::one()}else{Fr::zero()};
        match origin.label {
            "serializer_boolean_diagonal"=>{
                assert_eq!(item.term.gate.left,item.term.gate.right,
                    "C429 Boolean original right endpoint changed ordinal={}",item.ordinal);
                assert_eq!((item.term.gate.c1,item.term.gate.c3),(-Fr::one(),Fr::one()),
                    "C429 Boolean polynomial tuple changed ordinal={}",item.ordinal);
                assert_eq!(weighted_a*left_bit,Fr::zero(),
                    "C429 Boolean identity z*(z-1)=0 failed ordinal={}",item.ordinal);
            }
            "serializer_input_padding"=>{
                assert_eq!(right,SERIALIZER_WIRE_BASE,
                    "C429 padding original right endpoint differs from owner-local X base");
                assert_eq!((item.term.gate.c1,item.term.gate.c3),(Fr::one(),Fr::zero()),
                    "C429 padding polynomial tuple changed ordinal={}",item.ordinal);
                assert_eq!(left_bit,Fr::zero(),
                    "C429 zero-padding packet bit is nonzero left={left}");
                assert_eq!(weighted_a*left_bit,Fr::zero(),
                    "C429 padding contribution was not zero left={left}");
            }
            other=>panic!("C429 unexpected source label {other} ordinal={}",item.ordinal),
        }
        verified_zero_family_terms+=1;
        cold_a[left]+=weighted_a;
        cold_b[left]+=weighted_b;
    }
    assert_eq!(verified_zero_family_terms,FAMILY_TERMS,
        "C429 claim_0 derivation omitted source-owned family terms");
    assert!(cold_b.iter().all(|value|value.is_zero()),
        "C429 source-derived cold B must be zero before p0");
    let mut cold_x=(0..WIDTH).map(|index|{
        if c427_packet_bit(packet,index){Fr::one()}else{Fr::zero()}
    }).collect::<Vec<_>>();
    let owner_p0=crate::gkr::quadratic_message(&cold_a,&cold_b,&cold_x);
    let owner_claim0=cold_a.iter().zip(&cold_b).zip(&cold_x)
        .map(|((a,b),x)|*a**x+*b).sum::<Fr>();
    assert_eq!(owner_claim0,Fr::zero(),
        "C429 one-owner claim_0 must be derived as zero from Boolean and zero-padding tuples");
    assert_eq!(owner_p0[0]+crate::gkr::eval_polynomial(&owner_p0,Fr::one()),owner_claim0,
        "C429 one-owner p0 sumcheck identity");
    let mut cold_claim=crate::gkr::eval_polynomial(&owner_p0,alpha);
    crate::gkr::fold(&mut cold_a,alpha);
    crate::gkr::fold(&mut cold_x,alpha);
    let zero_b=vec![Fr::zero();WIDTH/2];
    assert_eq!(cold_b.len(),WIDTH);
    assert!(cold_b.iter().all(|value|value.is_zero()));
    crate::gkr::fold(&mut cold_b,alpha);
    let claim_1=cold_a.iter().zip(&cold_b).zip(&cold_x)
        .map(|((a,b),x)|*a**x+*b).sum::<Fr>();
    assert_eq!(cold_claim,claim_1,
        "C429 one-owner claim_1=p0(alpha) must equal folded A/X/B state");

    let (mut hot_a,mut hot_x,stats)=c429_one_owner_byte_state(&point,alpha,owner,packet);
    c427_assert_fr_vectors(&cold_a,&hot_a,"C429 post-alpha A'");
    c427_assert_fr_vectors(&cold_b,&zero_b,"C429 post-alpha B'");
    c427_assert_fr_vectors(&cold_x,&hot_x,"C429 post-alpha X'");
    let mut hot_claim=hot_a.iter().zip(&hot_x).map(|(a,x)|*a**x).sum::<Fr>();
    assert_eq!(hot_claim,cold_claim,
        "C429 independent packet-derived hot claim_1 differs from cold p0(alpha)");
    let mut cold_transcript=prefix_after_alpha.clone();
    let mut hot_transcript=prefix_after_alpha;
    let counters_after_alpha=(cold_transcript.challenges(),cold_transcript.raw_queries(),
        cold_transcript.bytes_absorbed());
    assert_eq!(counters_after_alpha,(41,51,4_402));

    for round in 1..=19usize {
        assert_eq!(cold_claim,hot_claim,"C429 round {round} pre-message claim");
        let cold_message=crate::gkr::quadratic_message(&cold_a,&cold_b,&cold_x);
        let hot_message=crate::gkr::quadratic_message(&hot_a,&zero_b[..hot_a.len()],&hot_x);
        assert_eq!(cold_message,hot_message,"C429 round {round} first message divergence");
        assert_eq!(cold_message[0]+crate::gkr::eval_polynomial(&cold_message,Fr::one()),cold_claim,
            "C429 cold round {round} sumcheck identity");
        assert_eq!(hot_message[0]+crate::gkr::eval_polynomial(&hot_message,Fr::one()),hot_claim,
            "C429 hot round {round} sumcheck identity");

        crate::gkr::append_polynomial(&mut cold_transcript,b"gkr-sumcheck-polynomial",&cold_message);
        crate::gkr::append_polynomial(&mut hot_transcript,b"gkr-sumcheck-polynomial",&hot_message);
        let cold_challenge=cold_transcript.challenge_scalar(b"gkr-sumcheck-challenge");
        let hot_challenge=hot_transcript.challenge_scalar(b"gkr-sumcheck-challenge");
        assert_eq!(cold_challenge,hot_challenge,"C429 round {round} challenge");
        cold_claim=crate::gkr::eval_polynomial(&cold_message,cold_challenge);
        hot_claim=crate::gkr::eval_polynomial(&hot_message,hot_challenge);
        assert_eq!(cold_claim,hot_claim,"C429 round {round} post-message claim");

        crate::gkr::fold(&mut cold_a,cold_challenge);
        crate::gkr::fold(&mut cold_b,cold_challenge);
        crate::gkr::fold(&mut cold_x,cold_challenge);
        crate::gkr::fold(&mut hot_a,hot_challenge);
        crate::gkr::fold(&mut hot_x,hot_challenge);
        c427_assert_fr_vectors(&cold_a,&hot_a,&format!("C429 round {round} post-fold A"));
        c427_assert_fr_vectors(&cold_b,&zero_b[..cold_b.len()],&format!("C429 round {round} post-fold B"));
        c427_assert_fr_vectors(&cold_x,&hot_x,&format!("C429 round {round} post-fold X"));
        assert_eq!((cold_transcript.challenges(),cold_transcript.raw_queries(),cold_transcript.bytes_absorbed()),
            (hot_transcript.challenges(),hot_transcript.raw_queries(),hot_transcript.bytes_absorbed()),
            "C429 round {round} transcript counters");
    }
    assert_eq!(cold_a.len(),1);assert_eq!(hot_a.len(),1);
    assert_eq!(cold_x.len(),1);assert_eq!(hot_x.len(),1);
    assert_eq!(cold_claim,cold_a[0]*cold_x[0]+cold_b[0],"C429 cold terminal claim");
    assert_eq!(hot_claim,hot_a[0]*hot_x[0],"C429 hot terminal claim");
    assert_eq!(cold_claim,hot_claim);
    let final_counters=(cold_transcript.challenges(),cold_transcript.raw_queries(),
        cold_transcript.bytes_absorbed());
    assert_eq!(final_counters.0,60,"C429 final challenge counter after 19 rounds");
    assert!(final_counters.1>=70,"C429 raw query counter below one query per challenge");
    assert_eq!(final_counters.2,11_242,"C429 exact transcript byte counter after 19 rounds");
    let explicit_hot_state_bytes=stats.explicit_builder_bytes+
        zero_b.capacity()*std::mem::size_of::<Fr>();
    println!("C429 one-owner synthetic p1-p19 differential PRECODE={C429_ALL_ROUND_PRECODE_SHA256} owner={owner} family_terms={} packet_bytes={} claim_0=derived-zero claim_1=p0(alpha) prefix_after_alpha={counters_after_alpha:?} final_counters={final_counters:?} hot_packet_reads={} boolean_reads={} padding_reads={} sentinel_checks={} X_lut_lookups={} X_cell_writes={} active_A_writes={} explicit_hot_state_and_shared_B_bytes={} terminal_claim_le={} scope=synthetic-owner-slice-not-shared-four-owner-transcript-or-full-HEADER",
        FAMILY_TERMS,packet.len(),stats.packet_byte_reads,stats.boolean_family_byte_reads,
        stats.padding_byte_reads,stats.sentinel_checks,stats.x_lut_lookups,stats.x_cell_writes,
        stats.active_a_cell_writes,explicit_hot_state_bytes,c427_hex(&c427_fr_bytes(&hot_claim)));
}

const C429_FOUR_OWNER_COLD_PRECODE_R4_SHA256:&str="4955955D7EA2F8E7846E0F1CDB1235E5A8FBEC7790B6D747BAA1A399ABBA554C";

#[derive(Clone)]
struct C429ColdOwnerRecord {
    owner:u64, class_code:u64, active_mask:u64, source_count:u64, placed_count:u64,
    packet_bytes:u64, source_digest:[u8;32], placed_digest:[u8;32], packet_digest:[u8;32],
}
#[derive(Clone)]
struct C429ColdRoundRecord {round:u64, polynomial:[Fr;3], challenge:Fr, claim:Fr, counters:(u64,u64,u64)}
struct C429ColdReference {
    owners:Vec<C429ColdOwnerRecord>, packet_bundle_digest:[u8;32], payload_digest:[u8;32],
    point:Vec<Fr>, claim_0:Fr, p0:[Fr;3], alpha:Fr, claim_1:Fr,
    post_alpha_counters:(u64,u64,u64), rounds:Vec<C429ColdRoundRecord>,
    terminal_pairs:Vec<(Fr,Fr)>, terminal_claim:Fr,
}

fn c429_four_owner_cold_reference_data() -> C429ColdReference {
    // C427 family-only digests from the frozen four-owner family log (SHA-256 2D43B082...67B2C); these
    // are distinct from the broader C425 full-HEADER owner digests.
    const C427_FAMILY_DIGESTS:[(&str,&str);4]=[
        ("611971a8bfe4ff57c7c63ccbad3087a741caa98388e9fcb72ddd4d2096a1e709","f15d65609b6cfaa0695da638e281e5e93513e819d2fc3ea7c34c9c5eabc28059"),
        ("c047835d205c6a64b4c9ee2c5d92aa42c14992d17f9b978530d60f0a49a5e5c0","a6d8e12310bdcecc0274dfb5976c56e3ae9ef97bf3d9ab6604c449abe7fc22f7"),
        ("a63571f27d96a2ade65edb88bc86bc4bba8ab23162c93855be41994c00c8b2e2","8bd3dcfe599ee4944117f05e683738b14c73cce612b588324e29ed3fa9398e12"),
        ("924d5d5c5fc659abf53cb8a945c6daf133aa621cac8e6c99cdade42afcc3da52","83111aa7552b2b8c53aa64ce9a0b13f29109ca8166dfd19dcf56de1d299e5726"),
    ];
    let (packets,point,alpha,prefix_p0,prefix_claim_0,prefix_after_alpha)=c427_prefix_diagnostic();
    assert_eq!(packets.len(),4,"C429 cold reference packet count");
    assert_eq!(point.len(),40,"C429 cold reference point width");
    assert_eq!(prefix_claim_0,Fr::zero(),"C429 cold prefix claim_0 must be derived zero");
    assert_eq!((prefix_after_alpha.challenges(),prefix_after_alpha.raw_queries(),
        prefix_after_alpha.bytes_absorbed()),(41,51,4_402),"C429 cold post-alpha prefix counters");
    assert!(C425_OWNERS.windows(2).all(|pair|pair[0].0<pair[1].0),
        "C429 frozen owner order must be ascending");

    let (canonical,spans,origins)=canonical_family();
    assert_family_ledger(&canonical,&spans,&origins);
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[7;32],[0;28]).unwrap();
    let roster=DaaHistoryRoster::compile(&parent).unwrap();
    let schedule=Scheduled::eligible08();
    let row_plan=RowPlan::new(&roster,&schedule).unwrap();
    let local_weights=crate::gkr::eq_weights(&point[..19]);
    let mut owner_states=Vec::with_capacity(C425_OWNERS.len());
    let mut aggregate_p0=[Fr::zero();3];
    let mut aggregate_claim_0=Fr::zero();
    let mut source_term_count=0usize;
    let mut owner_records=Vec::with_capacity(C425_OWNERS.len());

    for (owner_index,&(owner,class,active)) in C425_OWNERS.iter().enumerate() {
        let packet=&packets[owner_index];
        assert_eq!(packet.len(),WIDTH/8,"C429 owner packet byte length owner={owner}");
        let placed=cold_owner_family_census(owner,class,active,&parent,&roster,&row_plan,
            &canonical,&spans,&origins);
        assert_eq!(placed.len(),FAMILY_TERMS,"C429 owner family occurrence count owner={owner}");
        assert_eq!(c427_ordinal_coverage(&placed,placed[0].ordinal),Ok(()),
            "C429 owner ordered global-source coverage owner={owner}");
        assert_eq!(origins[placed[0].ordinal].unwrap().label,"serializer_boolean_diagonal",
            "C429 owner Boolean source prefix owner={owner}");
        assert_eq!(origins[placed[BOOLEAN_TERMS].ordinal].unwrap().label,"serializer_input_padding",
            "C429 owner padding source boundary owner={owner}");

        let source_records=placed.iter().map(|item|{
            let source=super::globalize(owner,&canonical[item.ordinal])
                .unwrap_or_else(|error|panic!("C429 owner source tuple globalize owner={owner}: {error}"));
            (item.ordinal,source,item.term.clone())
        }).collect::<Vec<_>>();
        let (source_digest,placed_digest)=crate::c425_span_census::c427_owner_sha256(owner,&source_records)
            .unwrap_or_else(|error|panic!("C429 artifact owner tuple digest owner={owner}: {error}"));
        assert_eq!(source_digest,C427_FAMILY_DIGESTS[owner_index].0,
            "C429 owner family source tuple digest differs from frozen C427 cold ledger owner={owner}");
        assert_eq!(placed_digest,C427_FAMILY_DIGESTS[owner_index].1,
            "C429 owner family placed tuple digest differs from frozen C427 cold ledger owner={owner}");
        let class_code=match class {
            OwnerClass::Mature(Epoch::Legacy)=>0,
            OwnerClass::Carry=>1,
            OwnerClass::Mature(Epoch::Eip)=>2,
            OwnerClass::Padding=>3,
            other=>panic!("C429 schema has no class code for {other:?}"),
        };
        let active_mask=active.iter().enumerate().fold(0u64,|mask,(bit,set)|mask|((*set as u64)<<bit));
        let packet_digest=crate::native_prefix_auth_plan::role0_sha256(packet).unwrap();
        owner_records.push(C429ColdOwnerRecord{
            owner:owner as u64,class_code,active_mask,source_count:source_records.len() as u64,
            placed_count:placed.len() as u64,packet_bytes:packet.len() as u64,
            source_digest:c429_parse_sha256(&source_digest),placed_digest:c429_parse_sha256(&placed_digest),
            packet_digest,
        });

        let rho=c427_eq_scalar(&point[19..],owner);
        let mut a=vec![Fr::zero();WIDTH];
        let mut b=vec![Fr::zero();WIDTH];
        let x=(0..WIDTH).map(|index|{
            if c427_packet_bit(packet,index){Fr::one()}else{Fr::zero()}
        }).collect::<Vec<_>>();
        let mut term_claim_0=Fr::zero();
        for item in &placed {
            let q=item.term.row-owner*ROWS;
            let left=item.term.gate.left-owner*WIDTH;
            let right=item.term.gate.right-owner*WIDTH;
            let right_bit=if c427_packet_bit(packet,right){Fr::one()}else{Fr::zero()};
            let left_bit=if c427_packet_bit(packet,left){Fr::one()}else{Fr::zero()};
            let origin=origins[item.ordinal].expect("C429 source-owned family label");
            assert_eq!((item.term.gate.c0,item.term.gate.c2),(Fr::zero(),Fr::zero()),
                "C429 family B coefficients not source-zero owner={owner} ordinal={}",item.ordinal);
            let weighted_a= rho*local_weights[q]*
                (item.term.gate.c1+item.term.gate.c3*right_bit);
            let weighted_b= rho*local_weights[q]*
                (item.term.gate.c0+item.term.gate.c2*right_bit);
            assert_eq!(weighted_b,Fr::zero(),
                "C429 source-derived B contribution owner={owner} ordinal={}",item.ordinal);
            match origin.label {
                "serializer_boolean_diagonal"=>{
                    assert_eq!(item.term.gate.left,item.term.gate.right,
                        "C429 Boolean original right endpoint owner={owner} ordinal={}",item.ordinal);
                    assert_eq!((item.term.gate.c1,item.term.gate.c3),(-Fr::one(),Fr::one()),
                        "C429 Boolean source tuple owner={owner} ordinal={}",item.ordinal);
                    assert_eq!(right_bit,left_bit,
                        "C429 Boolean diagonal packet bit mismatch owner={owner} ordinal={}",item.ordinal);
                    assert_eq!(weighted_a*left_bit,Fr::zero(),
                        "C429 Boolean z*(z-1) term identity owner={owner} ordinal={}",item.ordinal);
                }
                "serializer_input_padding"=>{
                    assert_eq!(right,SERIALIZER_WIRE_BASE,
                        "C429 padding right endpoint is not owner-local X base owner={owner}");
                    assert_eq!((item.term.gate.c1,item.term.gate.c3),(Fr::one(),Fr::zero()),
                        "C429 padding source tuple owner={owner} ordinal={}",item.ordinal);
                    assert_eq!(left_bit,Fr::zero(),
                        "C429 zero padding packet bit owner={owner} left={left}");
                    assert_eq!(weighted_a*left_bit,Fr::zero(),
                        "C429 padding source term is nonzero owner={owner} ordinal={}",item.ordinal);
                }
                other=>panic!("C429 unexpected family source label {other} owner={owner} ordinal={}",item.ordinal),
            }
            term_claim_0+=weighted_a*left_bit+weighted_b;
            a[left]+=weighted_a;
            b[left]+=weighted_b;
            source_term_count+=1;
        }
        assert_eq!(term_claim_0,Fr::zero(),"C429 source-derived owner claim_0 owner={owner}");
        let owner_claim_0=a.iter().zip(&b).zip(&x)
            .map(|((a,b),x)|*a**x+*b).sum::<Fr>();
        assert_eq!(owner_claim_0,term_claim_0,
            "C429 owner source-term/vector claim_0 owner={owner}");
        aggregate_claim_0+=owner_claim_0;
        assert!(b.iter().all(|value|value.is_zero()),
            "C429 source-derived cold B is not zero owner={owner}");
        let owner_p0=crate::gkr::quadratic_message(&a,&b,&x);
        for (aggregate,coefficient) in aggregate_p0.iter_mut().zip(owner_p0) {
            *aggregate+=coefficient;
        }
        owner_states.push((a,b,x));
    }
    assert_eq!(source_term_count,C425_OWNERS.len()*FAMILY_TERMS,
        "C429 cold source family coverage across owners");
    assert_eq!(aggregate_claim_0,prefix_claim_0,"C429 cold aggregate claim_0 vs frozen prefix");
    c427_assert_fr_vectors(&prefix_p0,&aggregate_p0,"C429 cold aggregate p0 vs frozen prefix");
    assert_eq!(aggregate_p0[0]+crate::gkr::eval_polynomial(&aggregate_p0,Fr::one()),
        aggregate_claim_0,"C429 cold aggregate p0 identity");

    let mut claim=crate::gkr::eval_polynomial(&aggregate_p0,alpha);
    for (a,b,x) in &mut owner_states {
        crate::gkr::fold(a,alpha);
        crate::gkr::fold(b,alpha);
        crate::gkr::fold(x,alpha);
    }
    let claim_1=owner_states.iter().map(|(a,b,x)|{
        a.iter().zip(b).zip(x).map(|((a,b),x)|*a**x+*b).sum::<Fr>()
    }).sum::<Fr>();
    assert_eq!(claim_1,claim,"C429 aggregate claim_1=p0(alpha) vs four folded states");

    let mut transcript=prefix_after_alpha;
    let post_alpha_counters=(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed());
    let mut rounds=Vec::with_capacity(19);
    for round in 1..=19usize {
        let before=(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed());
        let mut aggregate=[Fr::zero();3];
        for (a,b,x) in &owner_states {
            let owner_message=crate::gkr::quadratic_message(a,b,x);
            for (sum,coefficient) in aggregate.iter_mut().zip(owner_message) {
                *sum+=coefficient;
            }
        }
        assert_eq!(aggregate[0]+crate::gkr::eval_polynomial(&aggregate,Fr::one()),claim,
            "C429 shared cold round {round} sumcheck identity");
        crate::gkr::append_polynomial(&mut transcript,b"gkr-sumcheck-polynomial",&aggregate);
        let challenge=transcript.challenge_scalar(b"gkr-sumcheck-challenge");
        claim=crate::gkr::eval_polynomial(&aggregate,challenge);
        for (a,b,x) in &mut owner_states {
            crate::gkr::fold(a,challenge);
            crate::gkr::fold(b,challenge);
            crate::gkr::fold(x,challenge);
        }
        let folded_claim=owner_states.iter().map(|(a,b,x)|{
            a.iter().zip(b).zip(x).map(|((a,b),x)|*a**x+*b).sum::<Fr>()
        }).sum::<Fr>();
        assert_eq!(folded_claim,claim,
            "C429 shared cold round {round} post-fold aggregate claim");
        let after=(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed());
        assert_eq!(after.0,before.0+1,"C429 shared round {round} challenge counter");
        assert!(after.1>before.1,"C429 shared round {round} raw query counter");
        assert_eq!(after.2,before.2+360,"C429 shared round {round} transcript byte increment");
        rounds.push(C429ColdRoundRecord{round:round as u64,polynomial:aggregate,challenge,claim,counters:after});
    }
    assert!(owner_states.iter().all(|(a,b,x)|a.len()==1&&b.len()==1&&x.len()==1),
        "C429 cold terminal state width");
    let terminal_claim=owner_states.iter().map(|(a,b,x)|a[0]*x[0]+b[0]).sum::<Fr>();
    assert_eq!(terminal_claim,claim,"C429 cold terminal aggregate claim");
    let final_counters=(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed());
    assert_eq!(final_counters.0,60,"C429 four-owner cold final challenge count");
    assert!(final_counters.1>=70,"C429 four-owner cold raw-query lower bound");
    assert_eq!(final_counters.2,11_242,"C429 four-owner cold final transcript bytes");
    let terminal_pairs=owner_states.iter().map(|(a,_,x)|(a[0],x[0])).collect::<Vec<_>>();
    let (packets_for_binding,bundle)=c427_packet_fixture();
    assert_eq!(packets_for_binding.len(),packets.len(),"C429 artifact packet owner count");
    for (owner_index,(regenerated,original)) in packets_for_binding.iter().zip(&packets).enumerate() {
        assert_eq!(regenerated.len(),original.len(),"C429 artifact packet length owner_index={owner_index}");
        let digest=crate::native_prefix_auth_plan::role0_sha256(regenerated).unwrap();
        assert_eq!(digest,owner_records[owner_index].packet_digest,
            "C429 artifact regenerated packet digest owner_index={owner_index}");
    }
    assert_eq!(bundle.as_slice(),&c427_hex32("9FB01DB391141142AE464981249CD2E1FA3DC66BA0C145C963B7ED8981C969DD")[..],
        "C429 artifact regenerated pinned packet bundle digest");
    let payload=c427_binding_payload(&bundle);
    C429ColdReference{
        owners:owner_records,packet_bundle_digest:bundle.try_into().expect("C429 bundle digest width"),
        payload_digest:crate::native_prefix_auth_plan::role0_sha256(&payload).unwrap(),point,
        claim_0:aggregate_claim_0,p0:aggregate_p0,alpha,claim_1,post_alpha_counters,
        rounds,terminal_pairs,terminal_claim,
    }
}

#[test]
fn c429_four_owner_cold_shared_p1_through_p19_reference() {
    let reference=c429_four_owner_cold_reference_data();
    println!("C429 four-owner cold shared rounds PRECODE={C429_FOUR_OWNER_COLD_PRECODE_R4_SHA256} owners={} family_terms_per_owner={} claim_0=derived-zero claim_1=p0(alpha) rounds={} post_alpha_counters={:?} final_counters={:?} terminal_claim_le={} scope=cold-source-reference-only-no-hot-cost-claim",
        reference.owners.len(),FAMILY_TERMS,reference.rounds.len(),reference.post_alpha_counters,
        reference.rounds.last().unwrap().counters,c427_hex(&c427_fr_bytes(&reference.terminal_claim)));
}

fn c429_parse_sha256(value:&str)->[u8;32] {
    let raw=value.as_bytes();
    assert_eq!(raw.len(),64,"C429 SHA-256 env/digest width");
    let digit=|byte:u8|match byte {
        b'0'..=b'9'=>byte-b'0',b'a'..=b'f'=>byte-b'a'+10,b'A'..=b'F'=>byte-b'A'+10,
        _=>panic!("C429 invalid SHA-256 hex"),
    };
    let mut result=[0u8;32];
    for (index,pair) in raw.chunks_exact(2).enumerate(){result[index]=(digit(pair[0])<<4)|digit(pair[1]);}
    result
}

fn c429_env_sha256(name:&str)->([u8;32],String) {
    let value=std::env::var(name).unwrap_or_else(|_|panic!("C429 required runner environment pin absent: {name}"));
    let bytes=c429_parse_sha256(&value);
    (bytes,c427_hex(&bytes))
}

fn c429_append_u64(out:&mut Vec<u8>,value:u64){out.extend_from_slice(&value.to_le_bytes());}
fn c429_append_fr(out:&mut Vec<u8>,value:&Fr){
    assert_eq!(Fr::from_bigint(value.into_bigint()),Some(*value),"C429 noncanonical Fr before serialization");
    out.extend_from_slice(&c427_fr_bytes(value));
}

#[test]
fn c429_four_owner_cold_reference_artifact_writer() {
    const DOMAIN:&[u8]=b"C429-H21-HEADER-U-k1-COLD-REFERENCE\0";
    let supplied_output=std::env::var("C429_COLD_ARTIFACT_OUTPUT")
        .expect("C429_COLD_ARTIFACT_OUTPUT must be supplied by the reviewed runner");
    let output=std::path::Path::new(&supplied_output);
    assert!(crate::preview_test_paths::absolute_outside_source(output),"C429 artifact output root must be absolute and outside source");
    assert!(!output.exists(),"C429 artifact output root already exists; create-only attempt refused");
    let source_manifest=c429_env_sha256("C429_SOURCE_MANIFEST_SHA256");
    let test_source=c429_env_sha256("C429_COLD_TEST_SOURCE_SHA256");
    let runner=c429_env_sha256("C429_COLD_RUNNER_SHA256");
    let cargo_lock=c429_env_sha256("C429_CARGO_LOCK_SHA256");
    let c397=c429_env_sha256("C429_C397_SOURCE_CLOSURE_SHA256");
    let precode=c429_env_sha256("C429_PRECODE_R4_SHA256");
    assert_eq!(c397.0,c429_parse_sha256(C397_SOURCE_CLOSURE_SHA256),"C429 runner C397 closure pin");
    assert_eq!(precode.0,c429_parse_sha256(C429_FOUR_OWNER_COLD_PRECODE_R4_SHA256),"C429 runner PRECODE r4 pin");
    let compile_receipt=c429_env_sha256("C429_COLD_COMPILE_RECEIPT_SHA256");
    let executable=c429_env_sha256("C429_COLD_TEST_EXECUTABLE_SHA256");

    let reference=c429_four_owner_cold_reference_data();
    assert_eq!(reference.owners.len(),4);assert_eq!(reference.point.len(),40);
    assert_eq!(reference.rounds.len(),19);assert_eq!(reference.terminal_pairs.len(),4);
    assert_eq!(reference.post_alpha_counters,(41,51,4_402));
    assert_eq!(reference.rounds.last().unwrap().counters,(60,78,11_242));
    assert_eq!(reference.owners.iter().map(|owner|owner.source_count).collect::<Vec<_>>(),vec![131_072;4]);
    assert_eq!(reference.owners.iter().map(|owner|owner.placed_count).collect::<Vec<_>>(),vec![131_072;4]);
    assert_eq!(reference.owners.iter().map(|owner|owner.packet_bytes).collect::<Vec<_>>(),vec![131_072;4]);
    assert_eq!(reference.owners.iter().map(|owner|owner.owner).collect::<Vec<_>>(),vec![843_776,845_759,1_048_576,1_827_840]);

    let mut artifact=Vec::with_capacity(6_396);
    assert_eq!(DOMAIN.len(),36,"C429 fixed domain byte count");
    artifact.extend_from_slice(DOMAIN);
    c429_append_u64(&mut artifact,1);
    for count in [4u64,131_072,131_072,131_072,40,3,19,3,3,4,2]{c429_append_u64(&mut artifact,count);}
    for pin in [source_manifest.0,test_source.0,runner.0,cargo_lock.0,c397.0,precode.0]{artifact.extend_from_slice(&pin);}
    for owner in &reference.owners {
        for value in [owner.owner,owner.class_code,owner.active_mask,owner.source_count,owner.placed_count,owner.packet_bytes]{
            c429_append_u64(&mut artifact,value);
        }
        artifact.extend_from_slice(&owner.source_digest);
        artifact.extend_from_slice(&owner.placed_digest);
        artifact.extend_from_slice(&owner.packet_digest);
    }
    artifact.extend_from_slice(&reference.packet_bundle_digest);
    artifact.extend_from_slice(&reference.payload_digest);
    for coordinate in &reference.point{c429_append_fr(&mut artifact,coordinate);}
    c429_append_fr(&mut artifact,&reference.claim_0);
    for coefficient in &reference.p0{c429_append_fr(&mut artifact,coefficient);}
    c429_append_fr(&mut artifact,&reference.alpha);
    c429_append_fr(&mut artifact,&reference.claim_1);
    for value in [reference.post_alpha_counters.0,reference.post_alpha_counters.1,reference.post_alpha_counters.2]{c429_append_u64(&mut artifact,value);}
    for round in &reference.rounds {
        c429_append_u64(&mut artifact,round.round);
        for coefficient in &round.polynomial{c429_append_fr(&mut artifact,coefficient);}
        c429_append_fr(&mut artifact,&round.challenge);
        c429_append_fr(&mut artifact,&round.claim);
        for value in [round.counters.0,round.counters.1,round.counters.2]{c429_append_u64(&mut artifact,value);}
    }
    for (a,x) in &reference.terminal_pairs{c429_append_fr(&mut artifact,a);c429_append_fr(&mut artifact,x);}
    c429_append_fr(&mut artifact,&reference.terminal_claim);
    assert_eq!(artifact.len(),6_396,"C429 cold artifact schema r2 exact length");

    std::fs::create_dir(output).expect("C429 create-only artifact output root");
    let binary_path=output.join("cold-reference-v1.bin");
    let mut binary=std::fs::OpenOptions::new().write(true).create_new(true).open(&binary_path)
        .expect("C429 create-new cold binary");
    use std::io::Write;
    binary.write_all(&artifact).expect("C429 write cold binary");
    binary.sync_all().expect("C429 sync cold binary");
    drop(binary);
    let written=std::fs::read(&binary_path).expect("C429 reread written cold binary");
    assert_eq!(written.len(),6_396,"C429 durable binary length");
    let binary_sha=crate::native_prefix_auth_plan::role0_sha256(&written).unwrap();
    let receipt=serde_json::json!({
        "schema":1,
        "status":"PASS",
        "artifactFile":"cold-reference-v1.bin",
        "byteLength":written.len(),
        "artifactSHA256":c427_hex(&binary_sha),
        "inputPins":{
            "sourceManifestSHA256":source_manifest.1,
            "coldTestSourceSHA256":test_source.1,
            "runnerSHA256":runner.1,
            "cargoLockSHA256":cargo_lock.1,
            "c397SourceClosureSHA256":c397.1,
            "precodeR4SHA256":precode.1
        },
        "coldCompileReceiptSHA256":compile_receipt.1,
        "coldTestExecutableSHA256":executable.1,
        "counts":{"owners":4,"sourceFamilyTermsPerOwner":131072,"placedFamilyTermsPerOwner":131072,
            "packetBytesPerOwner":131072,"pointCoordinates":40,"p0Coefficients":3,"rounds":19,
            "coefficientsPerRound":3,"transcriptCountersPerSnapshot":3,"terminalOwners":4,"terminalFrCellsPerOwner":2}
    });
    let mut receipt_bytes=serde_json::to_vec_pretty(&receipt).expect("C429 encode detached receipt");
    receipt_bytes.push(b'\n');
    let receipt_path=output.join("cold-reference-receipt.json");
    let mut receipt_file=std::fs::OpenOptions::new().write(true).create_new(true).open(&receipt_path)
        .expect("C429 create-new detached receipt");
    receipt_file.write_all(&receipt_bytes).expect("C429 write detached receipt");
    receipt_file.sync_all().expect("C429 sync detached receipt");
    println!("C429 cold artifact durable bytes={} sha256={} receipt_bytes={} output_root={} input_pins=6 rounds={} owners={} scope=cold-four-owner-reference-only-no-hot-or-full-HEADER-claim",
        written.len(),c427_hex(&binary_sha),receipt_bytes.len(),supplied_output,reference.rounds.len(),reference.owners.len());
}

const C429_PRECODE_R3_SHA256:&str="D5151C9633A8A87B7E47B435563CE9EE6EEA522C69459759D36AB7B3E3FF2F30";

#[test]
fn c429_r3_all_byte_boolean_and_x_fold_formula_differential() {
    let low_row=[Fr::from(3u64),Fr::from(5u64),Fr::from(7u64)];
    let alpha=Fr::from(17u64);
    let chi=[Fr::one()-alpha,alpha];
    let eq=(0..8usize).map(|b|c427_eq_scalar(&low_row,b)).collect::<Vec<_>>();

    for raw in 0..256usize {
        let bits=(0..8usize).map(|b|Fr::from(((raw>>b)&1) as u64)).collect::<Vec<_>>();
        let mut c397_a=eq.iter().zip(&bits).map(|(&weight,&bit)|weight*(bit-Fr::one())).collect::<Vec<_>>();
        let mut c397_x=bits.clone();
        crate::gkr::fold(&mut c397_a,alpha);
        crate::gkr::fold(&mut c397_x,alpha);
        assert_eq!(c397_a.len(),4);
        assert_eq!(c397_x.len(),4);

        for h in 0..4usize {
            let expected_bool=(0..2usize).map(|offset|{
                let b=2*h+offset;
                chi[offset]*eq[b]*(bits[b]-Fr::one())
            }).sum::<Fr>();
            let expected_x=bits[2*h]+alpha*(bits[2*h+1]-bits[2*h]);
            assert_eq!(c397_a[h],expected_bool,
                "C429 r3 T_bool mismatch raw={raw} h={h}");
            assert_eq!(c397_x[h],expected_x,
                "C429 r3 T_X mismatch raw={raw} h={h}");
        }
    }

    let zero_byte=(0..8usize).map(|_|Fr::zero()).collect::<Vec<_>>();
    let mut c397_padding_a=eq.clone();
    crate::gkr::fold(&mut c397_padding_a,alpha);
    for h in 0..4usize {
        let expected_pad=(0..2usize).map(|offset|{
            let b=2*h+offset;chi[offset]*eq[b]
        }).sum::<Fr>();
        assert_eq!(c397_padding_a[h],expected_pad,"C429 r3 T_pad mismatch h={h}");
        assert_ne!(c397_padding_a[h],Fr::zero(),"C429 r3 zero-byte padding A' vanished h={h}");
        assert_eq!(zero_byte[h],Fr::zero());
    }
    println!("C429 r3 byte fold formula differential PRECODE={C429_PRECODE_R3_SHA256} raw_bytes=256 folded_outputs_per_byte=4 T_bool=passed T_X=passed zero_byte_T_pad_nonzero=passed");
}

#[test]
fn c429_r3_padding_drop_mutant_first_diverges_at_p4() {
    let point=(0..40usize).map(|i|Fr::from((2*i+3) as u64)).collect::<Vec<_>>();
    let owner=843_776usize;
    let challenges=[17u64,19,23,29].map(Fr::from);
    let owner_weight=c427_eq_scalar(&point[19..],owner);
    let row_weights=crate::gkr::eq_weights(&point[..19]);
    let mut with_padding=vec![Fr::zero();32];
    let without_padding=vec![Fr::zero();32];
    let mut x=vec![Fr::zero();32];
    // This window is family offsets [69664,69696): used [0,16), padding [16,32).
    for window_offset in 16..32usize {
        let family_offset=69_664+window_offset;
        let source_row=SERIALIZER_ROW_BASE+ATTACHED_ROW_OFFSET+family_offset;
        with_padding[window_offset]=owner_weight*row_weights[source_row];
    }
    x[15]=Fr::one(); // the only set bit is family offset 69679
    assert_eq!(SERIALIZER_ROW_BASE+ATTACHED_ROW_OFFSET+69_680,105_272);
    assert_eq!(SERIALIZER_ROW_BASE+ATTACHED_ROW_OFFSET+69_695,105_287);

    // alpha=17 folds the original 32 cells into the state for p1.
    crate::gkr::fold(&mut with_padding,challenges[0]);
    crate::gkr::fold(&mut x,challenges[0]);
    let mut padding_mutant=without_padding;
    crate::gkr::fold(&mut padding_mutant,challenges[0]);
    for (round,challenge) in challenges[1..].iter().copied().enumerate() {
        let full=crate::gkr::quadratic_message(&with_padding,&vec![Fr::zero();with_padding.len()],&x);
        let mutant=crate::gkr::quadratic_message(&padding_mutant,&vec![Fr::zero();padding_mutant.len()],&x);
        assert_eq!(full,mutant,"C429 r3 padding mutant changed p{}",round+1);
        crate::gkr::fold(&mut with_padding,challenge);
        crate::gkr::fold(&mut padding_mutant,challenge);
        crate::gkr::fold(&mut x,challenge);
    }

    let zero_b=vec![Fr::zero();with_padding.len()];
    let full=crate::gkr::quadratic_message(&with_padding,&zero_b,&x);
    let mutant=crate::gkr::quadratic_message(&padding_mutant,&zero_b,&x);
    let delta=full.iter().zip(&mutant).map(|(a,b)|*a-*b).collect::<Vec<_>>();
    assert_eq!(delta.len(),3);
    assert_eq!(delta[0],Fr::zero(),"C429 r3 padding p4 delta m0");
    assert_eq!(c427_fr_bytes(&delta[1]),c427_hex32(
        "00000000000044B7A7618A14B308F9AB6665A6C03AADBD78746A03CBE7140000"),
        "C429 r3 padding p4 delta m1");
    assert_eq!(delta[2],-delta[1],"C429 r3 padding p4 delta m2");
    println!("C429 r3 padding-drop mutant PRECODE={C429_PRECODE_R3_SHA256} owner={owner} family_bit=69679 source_padding_rows=105272..=105287 challenges=17,19,23,29 p1_p3_equal=true p4_delta_m0=0 p4_delta_m1_le={} p4_delta_m2=-m1",
        c427_hex(&c427_fr_bytes(&delta[1])));
}

