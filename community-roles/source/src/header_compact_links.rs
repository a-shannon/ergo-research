//! Compact projections of the two mandatory header adjacency relations.
//! Both links use one global header commitment; returned claims are global.
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use std::ops::Range;
use crate::{gkr::{Gate,GkrProof,InputClaim},header_order,
    packed::PackedFile,segment_adjacency::{Relation,StreamStats},segment_relation,
    serializer,sparse::Term,transcript::Transcript};

pub const HASH_OFFSET:usize=795648;
pub const HASH_WIDTH:usize=512;
const META_BANK:usize=1552;
const HASH_BANK:usize=1554;

pub struct Joined {
    pub base:Box<header_order::Joined>,
    pub released_rows:Range<usize>,
    pub alias_rows:Range<usize>,
}

pub fn build(fields:Option<&serializer::Fields>)->Result<Joined,String> {
    let mut base=Box::new(header_order::build(fields)?);
    let old=&mut base.base.base;
    let z=Fr::zero();let o=Fr::one();
    if old.boundary.terms.len()!=420841 || base.genesis_rows!=(405862..405894)
        || old.remaining_padding_rows.end!=405784 {
        return Err("compact adapter old boundary shape changed".into());
    }
    let padding_wire=segment_relation::DIGEST_OFFSET+256;
    let start=old.remaining_padding_rows.start+HASH_OFFSET-padding_wire;
    let released_rows=start..start+HASH_WIDTH;
    if released_rows!=(152856..153368) || released_rows.end>old.remaining_padding_rows.end {
        return Err("compact hash bank outside exact padding".into());
    }
    let first=old.boundary.terms.partition_point(|term|term.row<released_rows.start);
    for bit in 0..HASH_WIDTH {
        let expected=Term {row:start+bit,gate:Gate {left:HASH_OFFSET+bit,right:0,c0:z,c1:o,c2:z,c3:z}};
        if old.boundary.terms.get(first+bit)!=Some(&expected) {
            return Err("compact adapter expected exact zero anchor".into());
        }
    }
    for term in &mut old.boundary.terms[first..first+HASH_WIDTH] {
        term.gate=Gate {left:0,right:0,c0:z,c1:z,c2:z,c3:z};
    }
    let alias_rows=405894..406406;
    let alias_term_start=old.boundary.terms.len();
    for bit in 0..HASH_WIDTH {
        let source=if bit<256 {old.parent_wires[bit]} else {old.digest_wires[bit-256]};
        old.boundary.terms.push(Term {row:alias_rows.start+bit,
            gate:Gate {left:HASH_OFFSET+bit,right:source,c0:z,c1:o,c2:-o,c3:z}});
    }
    #[cfg(test)]
    crate::c425_span_census::append_source_span(
        "header_compact_links.build.hash_alias_terms", alias_term_start, old.boundary.terms.len());
    if old.boundary.terms.len()!=421353 || alias_rows.end!=406406 {
        return Err("compact adapter boundary count changed".into());
    }
    if let Some(input)=old.input.as_mut() {
        if input.len()!=segment_relation::HEADER_WIDTH {return Err("compact input width mismatch".into());}
        for bit in 0..HASH_WIDTH {
            let source=if bit<256 {old.parent_wires[bit]} else {old.digest_wires[bit-256]};
            input[HASH_OFFSET+bit]=input[source];
        }
    }
    Ok(Joined {base,released_rows,alias_rows})
}

pub fn assign_order(joined:&mut Joined,fields:&serializer::Fields,previous_height:u32,
    previous_time:i64,first:bool)->Result<(),String> {
    header_order::assign_order(&mut joined.base,fields,previous_height,previous_time,first)
}

pub fn embed(stage:usize,h:usize,point:&[Fr])->Result<Vec<Fr>,String> {
    if stage>=5 {return Err("compact link claims embed through Link".into());}
    header_order::embed(stage,h,point)
}
pub fn load_copy(source:&PackedFile,stage:usize,n:usize,copy:usize)->Result<Vec<Fr>,String> {
    if stage>=5 {return Err("compact link copies load through Link".into());}
    header_order::load_copy(source,stage,n,copy)
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum Role {Hash,Metadata}

/// The role, bank, and relation are inseparable at the public interface.
pub struct Link {relation:Relation,role:Role,bank:usize}

pub fn hash_relation(n:usize,tip:[u8;32])->Result<Link,String> {
    Ok(Link {relation:Relation::new_compact(n,[0;32],tip)?,role:Role::Hash,bank:HASH_BANK})
}
pub fn metadata_relation(n:usize,tip_time:i64)->Result<Link,String> {
    segment_relation::validate_n(n)?;
    let mut initial=[0u8;32];initial[12]=1;
    let mut terminal=[0u8;32];
    terminal[..4].copy_from_slice(&(n as u32).to_le_bytes());
    terminal[4..12].copy_from_slice(&tip_time.to_le_bytes());
    Ok(Link {relation:Relation::new_compact(n,initial,terminal)?,role:Role::Metadata,bank:META_BANK})
}

impl Link {
    pub fn input_log(&self)->usize {self.relation.input_log()}
    pub fn row_count(&self)->usize {self.relation.row_count()}
    pub fn global_input_log(&self)->usize {self.input_log()+11}

    fn embed_point(&self,point:&[Fr])->Result<Vec<Fr>,String> {
        if point.len()!=self.input_log() {return Err("compact link point dimensions invalid".into());}
        let mut out=Vec::with_capacity(self.global_input_log());
        out.extend_from_slice(&point[..9]);
        out.extend((0..11).map(|bit|Fr::from(((self.bank>>bit)&1) as u64)));
        out.extend_from_slice(&point[9..]);Ok(out)
    }
    fn global_claim(&self,mut claim:InputClaim)->Result<InputClaim,String> {
        claim.point=self.embed_point(&claim.point)?;Ok(claim)
    }
    fn bind_role(&self,transcript:&mut Transcript) {
        transcript.append_bytes(b"compact-link-role",match self.role {Role::Hash=>b"hash",Role::Metadata=>b"metadata"});
        transcript.append_u64(b"compact-link-bank",self.bank as u64);
        transcript.append_u64(b"compact-link-local-input-log",self.input_log() as u64);
        transcript.append_u64(b"compact-link-global-input-log",self.global_input_log() as u64);
        for bit in 0..11 {transcript.append_u64(b"compact-link-fixed-coordinate",((self.bank>>bit)&1) as u64);}
    }
    pub fn bind(&self,transcript:&mut Transcript) {
        self.bind_role(transcript);self.relation.bind(transcript);
    }
    pub fn prove_streamed_boolean(&self,source:&PackedFile,transcript:&mut Transcript)
        ->Result<(GkrProof,InputClaim,StreamStats),String> {
        if source.input_len()!=1usize<<self.global_input_log() {
            return Err("compact adjacency packed source dimension mismatch".into());
        }
        self.bind_role(transcript);
        let (proof,claim,stats)=self.relation.prove_compact_streamed_boolean(source,self.bank,transcript)?;
        Ok((proof,self.global_claim(claim)?,stats))
    }
    pub fn verify(&self,proof:&GkrProof,transcript:&mut Transcript)->Result<InputClaim,String> {
        self.bind_role(transcript);
        self.global_claim(self.relation.verify(proof,transcript)?)
    }
    pub fn decode_proof(&self,bytes:&[u8])->Result<GkrProof,String> {self.relation.decode_proof(bytes)}
}

#[cfg(test)]
mod tests {
    use super::*;
    use ergo_header_core::{Header,PowSolution};
    use crate::{gkr,header_hash,sparse::Circuit};
    use std::{fs::OpenOptions,io::Write};

    fn failed(c:&Circuit,input:&[Fr],omit:Option<Range<usize>>)->Vec<usize> {
        let mut rows=vec![Fr::zero();c.row_count];
        for term in &c.terms {
            if !omit.as_ref().is_some_and(|range|range.contains(&term.row)) {
                rows[term.row]+=term.gate.evaluate(input);
            }
        }
        rows.into_iter().enumerate().filter_map(|(row,value)|(!value.is_zero()).then_some(row)).collect()
    }
    fn retained(n:usize)->Vec<Header> {
        let pack:serde_json::Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
        (0..n).map(|i| {
            let text=pack["networks"]["mainnet"]["source_headers_hex"][i].as_str().unwrap();
            let raw:Vec<_>=text.as_bytes().chunks_exact(2).map(|pair|u8::from_str_radix(std::str::from_utf8(pair).unwrap(),16).unwrap()).collect();
            let digest=ergo_header_core::blake2b256(&raw);
            Header::decode(&raw,Some(&digest)).unwrap()
        }).collect()
    }
    fn fields(h:&Header)->serializer::Fields {
        let mut f=serializer::Fields {version:h.version,parent_id:h.parent_id,
            ad_proofs_root:h.ad_proofs_root,transactions_root:h.transactions_root,
            state_root:h.state_root,timestamp:h.timestamp,extension_root:h.extension_root,
            n_bits:h.n_bits,height:h.height,votes:h.votes,pk:[0;33],w:[0;33],
            nonce:[0;8],payload_len:0,payload:[0;255]};
        let payload=match &h.pow {
            PowSolution::V1 {pk,w,nonce,distance} => {
                f.pk=*pk.as_bytes();f.w=*w.as_bytes();f.nonce=*nonce;distance
            }
            PowSolution::V2 {pk,nonce} => {f.pk=*pk.as_bytes();f.nonce=*nonce;&h.unparsed_bytes}
        };
        f.payload_len=payload.len().try_into().unwrap();
        f.payload[..payload.len()].copy_from_slice(payload);f
    }
    fn joined(h:&Header,prev_height:u32,prev_time:i64,first:bool)->Joined {
        let f=fields(h);let mut j=build(Some(&f)).unwrap();
        assign_order(&mut j,&f,prev_height,prev_time,first).unwrap();j
    }
    fn local_old_pass(j:&Joined) {
        let x=j.base.base.base.input.as_ref().unwrap();
        for half in x[..header_hash::SERIALIZER_OFFSET].chunks_exact(1<<18) {
            assert!(failed(&j.base.base.base.core4,half,None).is_empty());
        }
        assert!(failed(&j.base.base.base.serializer.circuit,
            &x[header_hash::SERIALIZER_OFFSET..header_hash::AUX_OFFSET],None).is_empty());
        assert!(failed(&j.base.base.points.circuit,
            &x[crate::segment_points::POINT_OFFSET..crate::segment_points::POINT_OFFSET+crate::segment_points::POINT_WIDTH],None).is_empty());
        assert!(failed(&j.base.order.circuit,
            &x[header_order::ORDER_OFFSET..header_order::ORDER_OFFSET+header_order::ORDER_WIDTH],None).is_empty());
    }
    fn snapshot(t:&Transcript)->(u64,u64,u64,Fr) {
        let mut cloned=t.clone();
        (t.bytes_absorbed(),t.raw_queries(),t.challenges(),cloned.challenge_scalar(b"snapshot-next"))
    }
    fn set(bytes:&mut [u8],index:usize,value:bool) {
        let mask=1u8<<(index%8);
        if value {bytes[index/8]|=mask;} else {bytes[index/8]&=!mask;}
    }

    #[test]
    fn adapter_exact_anchors_aliases_and_private_assignment() {
        let h=retained(1).remove(0);let f=fields(&h);
        let public=build(None).unwrap();let mut j=build(Some(&f)).unwrap();
        assert!(public.base.base.base.input.is_none());
        assert_eq!(public.base.base.base.boundary,j.base.base.base.boundary);
        assert_eq!(j.released_rows,152856..153368);
        assert_eq!(j.alias_rows,405894..406406);
        assert_eq!(j.base.base.base.boundary.terms.len(),421353);
        let before=j.base.base.base.input.as_ref().unwrap().clone();
        assign_order(&mut j,&f,0,0,true).unwrap();
        let x=j.base.base.base.input.as_ref().unwrap();
        assert_eq!(&x[..header_order::ORDER_OFFSET],&before[..header_order::ORDER_OFFSET]);
        assert_eq!(&x[HASH_OFFSET..],&before[HASH_OFFSET..]);
        local_old_pass(&j);
        assert!(failed(&j.base.base.base.boundary,x,None).is_empty());
        for alias in 0..HASH_WIDTH {
            let source=if alias<256 {j.base.base.base.parent_wires[alias]}
                else {j.base.base.base.digest_wires[alias-256]};
            assert_eq!(x[HASH_OFFSET+alias],x[source]);
            assert_eq!(j.base.base.base.boundary.terms.iter()
                .filter(|term|term.row==j.alias_rows.start+alias).count(),1);
        }
        for alias in [0,255,256,511] {
            let mut changed=x.clone();changed[HASH_OFFSET+alias]=Fr::one()-changed[HASH_OFFSET+alias];
            assert_eq!(failed(&j.base.base.base.boundary,&changed,None),vec![j.alias_rows.start+alias]);
        }
        assert!(assign_order(&mut build(None).unwrap(),&f,0,0,true).is_err());
    }

    #[test]
    fn isolated_child_parent_alias_omission() {
        let mut hs=retained(2);let genesis=hs.remove(0);let mut child=hs.remove(0);
        let genesis_id=ergo_header_core::blake2b256(&genesis.encode().unwrap());
        assert_eq!(genesis_id,header_order::MAINNET_GENESIS);
        child.parent_id=genesis_id;child.parent_id[17]^=0x20;
        let tip=ergo_header_core::blake2b256(&child.encode().unwrap());
        let first=joined(&genesis,0,0,true);
        let mut second=joined(&child,1,genesis.timestamp,false);
        local_old_pass(&first);local_old_pass(&second);
        let a=first.base.base.base.input.as_ref().unwrap();
        let b=second.base.base.base.input.as_mut().unwrap();
        assert!(failed(&second.base.base.base.boundary,b,None).is_empty());
        let changed_alias=17*8+5;
        b[HASH_OFFSET+changed_alias]=a[HASH_OFFSET+256+changed_alias];
        let failures=failed(&second.base.base.base.boundary,b,None);
        assert_eq!(failures,vec![second.alias_rows.start+changed_alias]);
        assert!(failed(&second.base.base.base.boundary,b,
            Some(second.alias_rows.start+changed_alias..second.alias_rows.start+changed_alias+1)).is_empty());
        let mut packed=a.clone();packed.extend_from_slice(b);
        let link=hash_relation(2,tip).unwrap();
        let mut projected=Vec::with_capacity(1024);
        for header in 0..2 {for bit in 0..512 {
            projected.push(packed[header*(1<<20)+HASH_OFFSET+bit]);
        }}
        assert!(link.relation.residuals(&projected).unwrap().iter().all(Zero::is_zero));
    }

    #[test]
    fn compact_full_projection_preserves_arbitrary_field_residuals() {
        for n in [1usize,2,4] {
            let tip=[0x6a;32];let parent=[0x91;32];
            let full_parent=std::array::from_fn(|j|4096+j);
            let full_digest=std::array::from_fn(|j|8192+j);
            let full=Relation::new(n,full_parent,full_digest,parent,tip).unwrap();
            let compact=Relation::new_compact(n,parent,tip).unwrap();
            let mut global=vec![Fr::zero();n*(1<<20)];
            let mut projection=vec![Fr::zero();n*512];
            for header in 0..n {for bit in 0..512 {
                let value=Fr::from((header*997+bit*13+7) as u64);
                let wire=if bit<256 {full_parent[bit]} else {full_digest[bit-256]};
                global[header*(1<<20)+wire]=value;
                projection[header*512+bit]=value;
            }}
            assert_eq!(full.residuals(&global).unwrap(),compact.residuals(&projection).unwrap());
        }
    }

    #[test]
    fn compact_streamed_links_bind_roles_and_return_global_claims() {
        for n in [1usize,2,4] {
            let h=n.trailing_zeros() as usize;
            let mut packed:Vec<u8>=(0..n*(1<<20)/8)
                .map(|i|(i as u8).wrapping_mul(73).wrapping_add((i>>7) as u8)).collect();
            let tip=[0x63;32];let mut terminal=[0u8;32];
            terminal[..4].copy_from_slice(&(n as u32).to_le_bytes());
            terminal[4..12].copy_from_slice(&123i64.to_le_bytes());
            let mut initial=[0u8;32];initial[12]=1;
            let mut local_hash=vec![Fr::zero();n*512];
            let mut local_meta=vec![Fr::zero();n*512];
            for (bank,local,begin,end) in [
                (HASH_BANK,&mut local_hash,[0u8;32],tip),
                (META_BANK,&mut local_meta,initial,terminal),
            ] {
                let mut previous=[0u8;32];
                for header in 0..n {
                    let parent=if header==0 {begin} else {previous};
                    let digest=if header+1==n {end} else {std::array::from_fn(|byte|(header*17+byte*5+3) as u8)};
                    for bit in 0..256 {
                        let p=((parent[bit/8]>>(bit%8))&1)!=0;
                        let d=((digest[bit/8]>>(bit%8))&1)!=0;
                        local[header*512+bit]=Fr::from(p as u64);
                        local[header*512+256+bit]=Fr::from(d as u64);
                        set(&mut packed,header*(1<<20)+bank*512+bit,p);
                        set(&mut packed,header*(1<<20)+bank*512+256+bit,d);
                    }
                    previous=digest;
                }
            }
            let path=std::env::temp_dir().join(format!("compact-link-{}-{}-{}.bits",std::process::id(),n,
                std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
            let mut file=OpenOptions::new().write(true).create_new(true).open(&path).unwrap();
            file.write_all(&packed).unwrap();drop(file);
            let source=PackedFile::open(&path,20+h).unwrap();
            assert!(load_copy(&source,5,n,0).is_err());
            for (link,local) in [(hash_relation(n,tip).unwrap(),&local_hash),
                (metadata_relation(n,123).unwrap(),&local_meta)] {
                let mut dense_t=Transcript::new(b"compact-wrapper-parity");link.bind_role(&mut dense_t);
                let (dense_proof,dense_claim)=link.relation.prove(local,&mut dense_t).unwrap();
                let dense_claim=link.global_claim(dense_claim).unwrap();
                let mut streamed_t=Transcript::new(b"compact-wrapper-parity");
                let (proof,claim,stats)=link.prove_streamed_boolean(&source,&mut streamed_t).unwrap();
                assert_eq!(gkr::encode_proof(&proof).unwrap(),gkr::encode_proof(&dense_proof).unwrap());
                assert_eq!(claim,dense_claim);assert_eq!(snapshot(&streamed_t),snapshot(&dense_t));
                assert_eq!(stats.chunk_reads,22*n as u64);
                assert_eq!(stats.chunk_fields_max,512);assert_eq!(stats.transition_fields_max,3*n);
                assert_eq!(claim.point.len(),20+h);
                let mut verify_t=Transcript::new(b"compact-wrapper-parity");
                assert_eq!(link.verify(&link.decode_proof(&gkr::encode_proof(&proof).unwrap()).unwrap(),
                    &mut verify_t).unwrap(),claim);
                assert_eq!(snapshot(&verify_t),snapshot(&streamed_t));
                let mut preamble=Transcript::new(b"compact-binding");link.bind(&mut preamble);
                let mut manual=Transcript::new(b"compact-binding");
                link.bind_role(&mut manual);link.relation.bind(&mut manual);
                assert_eq!(snapshot(&preamble),snapshot(&manual));
                assert_eq!(source.evaluate(&claim.point).unwrap(),claim.value);
                for wrong_bank in [1553,if link.bank==META_BANK {HASH_BANK} else {META_BANK},
                    link.bank^(1<<3)] {
                    let mut wrong=claim.point.clone();
                    for bit in 0..11 {wrong[9+bit]=Fr::from(((wrong_bank>>bit)&1) as u64);}
                    assert_ne!(wrong,claim.point);
                    let wrong_value=source.evaluate(&wrong).unwrap();
                    assert_ne!(wrong_value,claim.value,"bank {wrong_bank} did not distinguish the fixture");
                }
                assert!(source.evaluate(&claim.point[..claim.point.len()-11]).is_err());
                if n==4 {
                    let mut swapped=claim.point.clone();swapped.swap(20,21);
                    assert_ne!(swapped,claim.point);
                    assert_ne!(source.evaluate(&swapped).unwrap(),claim.value);
                }
            }
            drop(source);std::fs::remove_file(path).unwrap();
        }
    }

    #[test]
    fn exact_embedding_rejects_other_banks_and_dimensions() {
        for n in [1usize,2,4] {
            let h=n.trailing_zeros() as usize;
            let hash=hash_relation(n,[0;32]).unwrap();let meta=metadata_relation(n,0).unwrap();
            assert_eq!(hash.input_log(),9+h);assert_eq!(hash.row_count(),512*n);
            assert_eq!(hash.global_input_log(),20+h);
            for link in [&hash,&meta] {
                let point:Vec<_>=(0..9+h).map(|i|Fr::from((i*7+3) as u64)).collect();
                let embedded=link.embed_point(&point).unwrap();
                assert_eq!(&embedded[..9],&point[..9]);assert_eq!(&embedded[20..],&point[9..]);
                for bit in 0..11 {assert_eq!(embedded[9+bit],Fr::from(((link.bank>>bit)&1) as u64));}
                assert!(link.embed_point(&point[..point.len()-1]).is_err());
                assert!(link.decode_proof(&[]).is_err());
            }
            let low:Vec<_>=(0..9).map(|bit|Fr::from(((17>>bit)&1) as u64)).collect();
            let mut point=low.clone();point.extend((0..h).map(|bit|Fr::from(((n-1>>bit)&1) as u64)));
            let hash_global=hash.embed_point(&point).unwrap();
            let meta_global=meta.embed_point(&point).unwrap();
            assert_ne!(hash_global,meta_global);
            let index=|p:&[Fr]|p.iter().enumerate().fold(0usize,|sum,(bit,x)|sum|((x.is_one() as usize)<<bit));
            assert_eq!(index(&hash_global),(n-1)*(1<<20)+HASH_OFFSET+17);
            assert_eq!(index(&meta_global),(n-1)*(1<<20)+header_order::ORDER_OFFSET+17);
            assert!(embed(5,h,&point).is_err());
        }
        assert!(hash_relation(3,[0;32]).is_err());assert!(metadata_relation(3,0).is_err());
    }
}
