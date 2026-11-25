use super::projection_aux_retirement::*;
use ark_bn254::Fr;
use ark_ff::{Field,One,Zero};
use crate::{gkr::Gate, serializer, sparse::{Circuit,Term}, transcript::Transcript};
use ergo_header_core::{GroupElement,Header,PowSolution};
use std::{cell::Cell,mem::size_of};

// Independent literal equality, including both complete Native input tags.
fn literal_eq(p:&[Fr],index:u64)->Fr{let mut out=Fr::one();for (b,x)in p.iter().enumerate(){
    out*=if (index>>b)&1==0{Fr::one()-x}else{*x};}out}
fn source_wire(a:&Authority,w:usize)->usize{let used=a.serializer().stats.used_input_bits;
    if used<=w && w<used+384{655628+w-used}else{524288+w}}
fn gate(c:[Fr;4],left:usize,right:usize)->Gate{Gate{left,right,c0:c[0],c1:c[1],c2:c[2],c3:c[3]}}
fn native_index(w:Native)->usize{((w.owner as usize)<<20)|w.local}
fn row_index(owner:u64,row:usize)->usize{(3usize<<32)|((owner as usize)<<12)|row}
fn bits(index:u64,n:usize)->Vec<Fr>{(0..n).map(|b|Fr::from((index>>b)&1)).collect()}
fn points(owner:u64,row:usize,left:usize,right:usize)->(Vec<Fr>,Vec<Fr>,Vec<Fr>){
    (bits(row_index(owner,row)as u64,34),bits(((owner as usize)<<20|left)as u64,41),
        bits(((owner as usize)<<20|right)as u64,41))}
fn canonical_layout(a:&Authority)->Layout<'_>{a.admit(&Descriptor::canonical(),&mappings(a.used()),
    &aliases(),a.certificate(),&a.projection().circuit).expect("actual source layout")}
fn mutate_term(t:&mut Term,k:usize){match k{0=>t.row+=1,1=>t.gate.left+=1,2=>t.gate.right+=1,
    3=>t.gate.c0+=Fr::one(),4=>t.gate.c1+=Fr::one(),5=>t.gate.c2+=Fr::one(),
    6=>t.gate.c3+=Fr::one(),_=>unreachable!()}}
fn rejected(a:&Authority,d:&Descriptor,m:&[Mapping],p:&[Alias],old:&[Term],c:&Circuit,e:Error){
    let calls=Cell::new(0usize);let result=a.admit_with(d,m,p,old,c,|_|{calls.set(calls.get()+1);});
    assert_eq!(result.err(),Some(e));assert_eq!(calls.get(),0,"metadata before semantic continuation");}

fn metadata_faults(a:&Authority)->usize{
    let d=Descriptor::canonical();let m=mappings(a.used());let p=aliases();
    let old=a.certificate();let c=&a.projection().circuit;let mut count=0;
    for i in 0..20{let mut bad=d.clone();bad.fields[i]+=1;
        rejected(a,&bad,&m,&p,old,c,Error::Descriptor(i));count+=1;}
    for i in 0..7{for b in 0..32{let mut bad=d.clone();bad.pins[i][b]^=1;
        rejected(a,&bad,&m,&p,old,c,Error::Pin(i));count+=1;}}
    for i in 0..384{
        let mut bad=m;bad[i].source+=1;rejected(a,&d,&bad,&p,old,c,Error::Map(i));count+=1;
        bad=m;bad[i].target+=1;rejected(a,&d,&bad,&p,old,c,Error::Map(i));count+=1;
        bad=m;bad[i]=m[(i+1)%384];rejected(a,&d,&bad,&p,old,c,Error::Map(i));count+=1;
        let missing:[Mapping;383]=std::array::from_fn(|j|m[j+usize::from(j>=i)]);
        rejected(a,&d,&missing,&p,old,c,Error::MapLength);count+=1;
    }
    for i in 0..32{for j in 0..5{let mut bad=p;bad[i].fields[j]+=1;
        rejected(a,&d,&m,&bad,old,c,Error::Port(i));count+=1;}
        let missing:[Alias;31]=std::array::from_fn(|j|p[j+usize::from(j>=i)]);
        rejected(a,&d,&m,&missing,old,c,Error::PortLength);count+=1;
        let mut bad=p;bad[i]=p[(i+1)%32];rejected(a,&d,&m,&bad,old,c,Error::Port(i));count+=1;
    }
    let mut changed=old.to_vec();assert_eq!(changed.capacity(),386);
    for i in 0..386{for k in 0..7{let original=changed[i].clone();mutate_term(&mut changed[i],k);
        rejected(a,&d,&m,&p,&changed,c,Error::Old(i));changed[i]=original;count+=1;}}
    rejected(a,&d,&m,&p,&changed[..385],c,Error::OldLength);count+=1;
    drop(changed);
    let extra=vec![old[0].clone();387];assert_eq!(extra.capacity(),387);
    rejected(a,&d,&m,&p,&extra,c,Error::OldLength);count+=1;drop(extra);
    let mut changed=c.clone();assert!(changed.terms.capacity()<=4096);
    changed.input_len+=1;rejected(a,&d,&m,&p,old,&changed,Error::Source);changed.input_len=c.input_len;count+=1;
    changed.row_count+=1;rejected(a,&d,&m,&p,old,&changed,Error::Source);changed.row_count=c.row_count;count+=1;
    let last=changed.terms.pop().unwrap();rejected(a,&d,&m,&p,old,&changed,Error::Source);
    changed.terms.push(last);count+=1;
    // Every actual ordered source tuple gets its own attributed corruption;
    // all row/axis/channel classes appear without another compiled template.
    for i in 0..PROJECTION_TERMS{let original=changed.terms[i].clone();mutate_term(&mut changed.terms[i],i%7);
        rejected(a,&d,&m,&p,old,&changed,Error::Projection(i));changed.terms[i]=original;count+=1;}
    changed.terms.swap(0,1);rejected(a,&d,&m,&p,old,&changed,Error::Projection(0));count+=1;
    drop(changed);assert_eq!(count,7091);count
}

fn local_reference(a:&Authority,owner:u64)->Vec<Term>{let mut out=Vec::with_capacity(TERMS);
    for t in &a.projection().circuit.terms{out.push(Term{row:row_index(owner,t.row),gate:Gate{
        left:((owner as usize)<<20)|source_wire(a,t.gate.left),
        right:((owner as usize)<<20)|source_wire(a,t.gate.right),
        c0:t.gate.c0,c1:t.gate.c1,c2:t.gate.c2,c3:t.gate.c3}});}
    for b in 0..32{out.push(Term{row:row_index(owner,1175+b),
        gate:gate([Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()],((owner as usize)<<20)|525650+b,(owner as usize)<<20)});
        out.push(Term{row:row_index(owner,1175+b),
            gate:gate([Fr::zero(),-Fr::one(),Fr::zero(),Fr::zero()],(((owner-1)as usize)<<20)|987162+b,(owner as usize)<<20)});}
    assert_eq!((out.len(),out.capacity()),(2443,2443));out}
fn literal_single(terms:&[Term],r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{let mut out=[Fr::zero();4];
    for t in terms{let w=literal_eq(r,t.row as u64)*literal_eq(u,t.gate.left as u64)*literal_eq(v,t.gate.right as u64);
        for (j,c)in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].iter().enumerate(){out[j]+=w*c;}}out}
fn literal_owner(r:&[Fr],u:&[Fr],v:&[Fr],offset:u64)->Fr{let mut out=Fr::zero();
    for h in 844671..845824{out+=literal_eq(r,h)*literal_eq(u,h-offset)*literal_eq(v,h);}out}
fn literal_all(a:&Authority,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{
    let native=literal_eq(&u[40..41],0)*literal_eq(&v[40..41],0);
    let family=literal_eq(&r[32..34],3);let k0=literal_owner(&r[12..32],&u[20..40],&v[20..40],0);
    let k1=literal_owner(&r[12..32],&u[20..40],&v[20..40],1);let mut out=[Fr::zero();4];
    for t in &a.projection().circuit.terms{let w=literal_eq(&r[..12],t.row as u64)
        *literal_eq(&u[..20],source_wire(a,t.gate.left)as u64)*literal_eq(&v[..20],source_wire(a,t.gate.right)as u64)*k0;
        for(j,c)in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].iter().enumerate(){out[j]+=w*c;}}
    for b in 0..32{let row=literal_eq(&r[..12],1175+b)*literal_eq(&v[..20],0);
        out[1]+=row*(k0*literal_eq(&u[..20],525650+b)-k1*literal_eq(&u[..20],987162+b));}
    for x in &mut out{*x*=native*family;}out}
fn literal_old(a:&Authority,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{
    let k=literal_owner(&r[19..39],&u[20..40],&v[20..40],0);let mut out=[Fr::zero();4];
    for t in &a.certificate()[1..385]{let w=literal_eq(&r[..19],t.row as u64)
        *literal_eq(&u[..20],t.gate.left as u64)*literal_eq(&v[..20],t.gate.right as u64)
        *literal_eq(&u[40..41],0)*literal_eq(&v[40..41],0)*k;
        for(j,c)in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].iter().enumerate(){out[j]+=w*c;}}out}

fn source_geometry(a:&Authority,l:Layout<'_>){
    let reference=local_reference(a,FIRST);assert_eq!(reference.capacity()*size_of::<Term>(),371336);
    let mut cursor=0;let mut channels=[0usize;4];
    for row in 0..4096{l.visit_row(FIRST,row,|t|{
        let expected=&reference[cursor];assert_eq!(expected.row,row_index(FIRST,row));
        assert_eq!(expected.gate,gate(t.c,native_index(t.left),native_index(t.right)));
        for(j,c)in t.c.iter().enumerate(){channels[j]+=usize::from(!c.is_zero());}cursor+=1;
    }).unwrap();}
    assert_eq!(cursor,2443);assert_eq!(channels,[1,1483,302,1897]);
    for owner in [FIRST-1,END,1048575]{for row in [0,1174,1175,1206,1207,4095]{
        let mut count=0;l.visit_row(owner,row,|_|count+=1).unwrap();assert_eq!(count,0);}}
    assert_eq!(l.visit_row(1<<20,0,|_|{}),Err(Error::Geometry));
    assert_eq!(l.visit_row(FIRST,4096,|_|{}),Err(Error::Geometry));
    let mut retired=0usize;for owner in FIRST..END{for old in OLD_FIRST..OLD_END{
        assert!(!l.retain_old(owner,OldBoundaryRow(old)));retired+=1;}
        assert!(l.retain_old(owner,OldBoundaryRow(OLD_FIRST-1)));
        assert!(l.retain_old(owner,OldBoundaryRow(OLD_END)));}
    assert_eq!(retired,442752);
    for owner in [FIRST-1,END,1048575]{for old in OLD_FIRST..OLD_END{assert!(l.retain_old(owner,OldBoundaryRow(old)));}}
    let mapped:[usize;384]=std::array::from_fn(|b|l.mapped(a.used()+b).unwrap());
    assert!(mapped.windows(2).all(|pair|pair[0]<pair[1]));
    assert!(mapped.iter().all(|w|!(OFFSET..OFFSET+WIDTH).contains(w)));
    for w in [0,1,a.used()-1,a.used()+384,WIDTH-1]{
        assert_eq!(l.mapped(w).unwrap(),OFFSET+w);assert_eq!(l.mapped(w).unwrap(),source_wire(a,w));}
    assert_eq!(l.mapped(WIDTH),Err(Error::Coordinate));
    for a0 in 0..384{assert_eq!(l.mapped(a.used()+a0),Ok(AUX+a0));}
    for (row,left,right,expected)in [(0,524288,524288,[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()]),
        (1,524289,524288,[-Fr::one(),Fr::one(),Fr::zero(),Fr::zero()]),
        (539,525386,525387,[Fr::zero(),Fr::one(),Fr::one(),-Fr::one()])]{
        let(r,mut u,mut v)=points(FIRST,row,left,right);
        assert_eq!(literal_single(&reference,&r,&u,&v),expected);
        assert_eq!(l.coefficients(&r,&u,&v).unwrap(),expected);
        for (ut,vt)in [(Fr::one(),Fr::zero()),(Fr::zero(),Fr::one()),(Fr::one(),Fr::one())]{
            u[40]=ut;v[40]=vt;assert_eq!(l.coefficients(&r,&u,&v).unwrap(),[Fr::zero();4]);
            assert_eq!(literal_single(&reference,&r,&u,&v),[Fr::zero();4]);}
        u[40]=Fr::from(2);v[40]=Fr::from(3);let doubled=expected.map(|x|x*Fr::from(2));
        assert_eq!(l.coefficients(&r,&u,&v).unwrap(),doubled);
        assert_eq!(literal_single(&reference,&r,&u,&v),doubled);
    }
    // Nonzero C1 addends cancel; the full vector retains a nonzero C0.
    let(mut r,mut u,v)=points(FIRST,0,524288,524288);r[0]=Fr::from(2);
    u[0]=Fr::from(3).inverse().unwrap();
    let expected=[-Fr::from(2)/Fr::from(3),Fr::zero(),Fr::zero(),Fr::zero()];
    assert_eq!(l.coefficients(&r,&u,&v).unwrap(),expected);
    assert_eq!(literal_single(&reference,&r,&u,&v),expected);
    let first=literal_eq(&r,row_index(FIRST,0)as u64)*literal_eq(&u,((FIRST<<20)+524288)as u64)
        *literal_eq(&v,((FIRST<<20)+524288)as u64);
    let second=literal_eq(&r,row_index(FIRST,1)as u64)*literal_eq(&u,((FIRST<<20)+524289)as u64)
        *literal_eq(&v,((FIRST<<20)+524288)as u64);
    assert_eq!((first,second),(-Fr::from(2)/Fr::from(3),Fr::from(2)/Fr::from(3)));
    assert!(!first.is_zero() && !second.is_zero());assert!((first+second).is_zero());
    drop(reference);
    // Complete non-Boolean points exercise tag, owner, family and local masks.
    for (rv,uv,vv)in [(2,3,4),(3,5,7),(7,11,13)]{
        let r=vec![Fr::from(rv)/Fr::from(17);34];let u=vec![Fr::from(uv)/Fr::from(19);41];
        let v=vec![Fr::from(vv)/Fr::from(23);41];
        assert_eq!(l.coefficients(&r,&u,&v).unwrap(),literal_all(a,&r,&u,&v));
        let old_r=vec![Fr::from(rv)/Fr::from(17);39];
        assert_eq!(l.retired_coefficients(&old_r,&u,&v).unwrap(),literal_old(a,&old_r,&u,&v));
    }
    for owner in [FIRST-1,FIRST,END-1,END]{let(r,u,v)=points(owner,0,524288,524288);
        let expected=if (FIRST..END).contains(&owner){Fr::one()}else{Fr::zero()};
        assert_eq!(l.coefficients(&r,&u,&v).unwrap()[1],expected);
        assert_eq!(l.coefficients(&r,&u,&v).unwrap(),literal_all(a,&r,&u,&v));}
    for family in [0u64,1,2]{let(mut r,u,v)=points(FIRST,0,524288,524288);
        r[32]=Fr::from(family&1);r[33]=Fr::from(family>>1);
        assert_eq!(l.coefficients(&r,&u,&v).unwrap(),[Fr::zero();4]);}
    let old_r=bits((FIRST<<19)+OLD_FIRST as u64,39);
    let mut u=bits((FIRST<<20)+AUX as u64,41);let mut v=bits(FIRST<<20,41);
    assert_eq!(l.retired_coefficients(&old_r,&u,&v).unwrap(),[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()]);
    for (ut,vt)in [(1,0),(0,1),(1,1)]{u[40]=Fr::from(ut);v[40]=Fr::from(vt);
        assert_eq!(l.retired_coefficients(&old_r,&u,&v).unwrap(),[Fr::zero();4]);}
    u[40]=Fr::from(2);v[40]=Fr::from(3);
    assert_eq!(l.retired_coefficients(&old_r,&u,&v).unwrap(),[Fr::zero(),Fr::from(2),Fr::zero(),Fr::zero()]);
    assert_eq!(l.coefficients(&[],&u,&v),Err(Error::PointDimension));
    assert_eq!(l.retired_coefficients(&[Fr::zero();34],&u,&v),Err(Error::PointDimension));
}

fn fields(height:u32,timestamp:i64)->serializer::Fields{serializer::Fields{version:4,
    parent_id:[0x11;32],ad_proofs_root:[0x22;32],transactions_root:[0x33;32],state_root:[0x44;33],
    timestamp,extension_root:[0x55;32],n_bits:0x043B9ACA,height,votes:[0x66,0x77,0x88],
    pk:[0;33],w:[0;33],nonce:[1,2,3,4,5,6,7,8],payload_len:0,payload:[0;255]}}
fn native(f:&serializer::Fields)->Vec<u8>{Header{version:f.version,parent_id:f.parent_id,
    ad_proofs_root:f.ad_proofs_root,transactions_root:f.transactions_root,state_root:f.state_root,
    timestamp:f.timestamp,extension_root:f.extension_root,n_bits:f.n_bits,height:f.height,votes:f.votes,
    unparsed_bytes:vec![],pow:PowSolution::V2{pk:GroupElement::from_bytes(f.pk).unwrap(),nonce:f.nonce}}
    .encode().unwrap()}
fn word(input:&[Fr],wires:&[usize])->u64{wires.iter().enumerate().fold(0,|n,(b,w)|{
    assert!(input[*w].is_zero() || input[*w].is_one());n|((input[*w].is_one()as u64)<<b)})}
fn serializer_rows(a:&Authority,input:&[Fr]){let mut row=0;let mut value=Fr::zero();let mut visited=0;
    for t in &a.serializer().circuit.terms{if t.row!=row{assert!(value.is_zero(),"original serializer row{row}");
        row=t.row;value=Fr::zero();}value+=t.gate.evaluate(input);visited+=1;}
    assert!(value.is_zero());assert_eq!(visited,315546);
    assert!(input[a.used()..].iter().all(|x|x.is_zero()));}
fn borrowed<'a>(owner:u64,original:&'a[Fr],projected:&'a[Fr],decoder:&'a[Fr;32],neighbors:&'a[Fr;2])->BorrowedWitness<'a>{
    BorrowedWitness{owner,original,projected,decoder,neighbors}}
fn old_residual(t:&Term,owner:u64,read:&impl Fn(Native)->Result<Fr,Error>)->Fr{
    // Genuine extracted source Gate; do not evaluate through a dense Native array.
    assert!(t.gate.c2.is_zero() && t.gate.c3.is_zero());
    t.gate.c0+t.gate.c1*read(Native{owner,local:t.gate.left}).unwrap()}

fn fixture(a:&Authority,l:Layout<'_>,height:u32,timestamp:i64,full_faults:bool)->usize{
    let owner=height as u64-1;let f=fields(height,timestamp);let raw=native(&f);
    assert_eq!(f.height as u64,owner+1,"fixture height; not a new relation anchor");
    let mut original=a.serializer().assign(&f);assert_eq!((original.len(),original.capacity()),(WIDTH,WIDTH));
    serializer_rows(a,&original);
    let length=word(&original,&a.serializer().layout.length)as usize;assert_eq!(length,raw.len());
    for (byte,indices)in a.serializer().layout.bytes[..length].iter().enumerate(){
        assert_eq!(word(&original,indices)as u8,raw[byte]);}
    let mut projected=a.projection().assign(&original).unwrap();
    assert_eq!((projected.len(),projected.capacity()),(WIDTH,WIDTH));
    let mut decoder=std::array::from_fn(|b|original[1362+b]);let mut neighbors=[Fr::zero();2];
    let w=borrowed(owner,&original,&projected,&decoder,&neighbors);
    assert_eq!(w.read(l,Native{owner:u64::MAX,local:DECODER}),Err(Error::Coordinate));
    assert_eq!(w.read(l,Native{owner:owner-1,local:DECODER}),Ok(decoder[0]));
    assert_eq!(w.read(l,Native{owner,local:0}),Err(Error::Coordinate));
    let admitted=Admitted::new(l,w).expect("working replacement");
    for b in 0..32{assert_eq!(admitted.bit(b).unwrap(),&decoder[b]);}
    assert_eq!(admitted.bit(32),Err(Error::Coordinate));
    let binding=admitted.binding();assert_eq!((binding.len(),binding.capacity()),(b"projection-aux-retirement-v1\n".len()+400,b"projection-aux-retirement-v1\n".len()+400));
    let mut literal=Vec::with_capacity(binding.len());literal.extend_from_slice(b"projection-aux-retirement-v1\n");
    let d=Descriptor::canonical();for x in d.fields{literal.extend_from_slice(&x.to_le_bytes());}
    for p in d.pins{literal.extend_from_slice(&p);}literal.extend_from_slice(&(a.used()as u64).to_le_bytes());
    literal.extend_from_slice(&owner.to_le_bytes());assert_eq!(binding,literal);drop(literal);
    let mut direct=Transcript::new(b"certified-modern-suffix-test");
    direct.append_bytes(b"projection-aux-retirement-layout",&binding);drop(binding);
    let mut actual=Transcript::new(b"certified-modern-suffix-test");admitted.bind(&mut actual);
    assert_eq!(actual.bytes_absorbed(),direct.bytes_absorbed());
    assert_eq!(actual.challenge_scalar(b"semantic-check"),direct.challenge_scalar(b"semantic-check"));
    assert_eq!(actual.challenges(),1);drop(admitted);
    let a0=(0..384).find(|b|!projected[a.used()+b].is_zero()).expect("nonzero actual source aux");
    let value=projected[a.used()+a0];assert!(!value.is_zero());
    let padding=a.serializer().circuit.terms.iter().find(|t|t.gate.left==a.used()+a0
        && t.gate.right==0 && t.gate.c0.is_zero() && t.gate.c1.is_one()
        && t.gate.c2.is_zero() && t.gate.c3.is_zero()).expect("actual original padding anchor");
    assert_eq!(padding.gate.evaluate(&original),Fr::zero());
    assert_eq!(padding.gate.evaluate(&projected),value,"old original serializer conflict");
    let w=borrowed(owner,&original,&projected,&decoder,&neighbors);
    let read=|wire|w.read(l,wire);
    assert_eq!(old_residual(&a.certificate()[a0+1],owner,&read),value,"old remapped anchor conflict");
    let mut restored_reject=false;let mut retained=0;
    for t in a.certificate(){let retain=l.retain_old(owner,OldBoundaryRow(t.row));
        if retain{assert!(old_residual(t,owner,&read).is_zero());retained+=1;}
        if t.row==OLD_FIRST+a0{restored_reject=!old_residual(t,owner,&read).is_zero();}}
    assert_eq!(retained,2);assert!(restored_reject);
    assert_eq!(Admitted::new(l,borrowed(owner,&[],&projected,&decoder,&neighbors)).err(),Some(Error::Framing));
    assert_eq!(Admitted::new(l,borrowed(owner,&original,&[],&decoder,&neighbors)).err(),Some(Error::Framing));
    for outside in [FIRST-1,END]{assert_eq!(Admitted::new(l,borrowed(outside,&original,&projected,&decoder,&neighbors)).err(),Some(Error::Geometry));}
    let pad=original[a.used()];original[a.used()]=Fr::one();
    assert_eq!(Admitted::new(l,borrowed(owner,&original,&projected,&decoder,&neighbors)).err(),Some(Error::Padding(a.used())));
    original[a.used()]=pad;
    for i in 0..2{neighbors[i]=Fr::one();
        let w=borrowed(owner,&original,&projected,&decoder,&neighbors);
        assert_eq!(old_residual(&a.certificate()[if i==0{0}else{385}],owner,&|wire|w.read(l,wire)),Fr::one());
        assert_eq!(Admitted::new(l,w).err(),Some(Error::Neighbor(i)));neighbors[i]=Fr::zero();}
    let mut faults=0;
    if full_faults{
        for a0 in 0..384{let wire=a.used()+a0;let old=projected[wire];projected[wire]=Fr::from(2);
            let defining=a.projection().circuit.terms.iter().find(|t|t.gate.left==wire
                && !t.gate.c1.is_zero() && t.gate.c2.is_zero() && t.gate.c3.is_zero()).unwrap();
            let w=borrowed(owner,&original,&projected,&decoder,&neighbors);
            let residual=l.residual(owner,defining.row,&|wire|w.read(l,wire)).unwrap();
            assert_eq!(residual,defining.gate.c1*(Fr::from(2)-old));assert!(!residual.is_zero());
            assert!(matches!(Admitted::new(l,w).err(),Some(Error::Residual(_))));
            projected[wire]=old;faults+=1;
        }
        for b in 0..32{let old=decoder[b];decoder[b]=Fr::from(2);
            assert_eq!(Admitted::new(l,borrowed(owner,&original,&projected,&decoder,&neighbors)).err(),Some(Error::Alias(b)));
            decoder[b]=old;faults+=1;
            let wire=1362+b;let old=original[wire];original[wire]=Fr::one()-old;
            let w=borrowed(owner,&original,&projected,&decoder,&neighbors);
            assert!(matches!(Admitted::new(l,w).err(),Some(Error::Residual(_))));original[wire]=old;faults+=1;
        }
        // Big-endian RAW byte positions, independently located from native framing.
        let timestamp_len=if timestamp<128{1}else{2};
        for b in 0..32{let byte=130+timestamp_len+32+(3-b/8);
            let wire=a.serializer().layout.bytes[byte][b%8];let old=original[wire];original[wire]=Fr::one()-old;
            assert!(matches!(Admitted::new(l,borrowed(owner,&original,&projected,&decoder,&neighbors)).err(),Some(Error::Residual(_))));
            original[wire]=old;faults+=1;}
        let old_decoder=decoder;decoder=std::array::from_fn(|b|Fr::from((f.n_bits.swap_bytes()>>b)&1));
        assert!(matches!(Admitted::new(l,borrowed(owner,&original,&projected,&decoder,&neighbors)).err(),Some(Error::Alias(_))));
        decoder=old_decoder;faults+=1;
        // Ordinary invalid rows cannot exploit a non-Boolean output weighting.
        let w=borrowed(owner,&original,&projected,&decoder,&neighbors);
        let base_read=|wire|w.read(l,wire);
        let read=|wire:Native|if wire.owner==owner && [OFFSET,OFFSET+1].contains(&wire.local){Ok(Fr::from(2))}else{base_read(wire)};
        assert_eq!(l.residual(owner,0,&read).unwrap(),Fr::from(2));
        assert_eq!(l.residual(owner,1,&read).unwrap(),Fr::one());
        assert_eq!(-l.residual(owner,0,&read).unwrap()+Fr::from(2)*l.residual(owner,1,&read).unwrap(),Fr::zero());
        assert_eq!(l.check(owner,&read),Err(Error::Residual(0)));faults+=1;
        // Semantic zero remains zero after a wrong formal right-axis mutation;
        // actual complete coefficient reference catches it.
        let(r,u,v)=points(owner,0,OFFSET,OFFSET);let mut correct=None;
        l.visit_row(owner,0,|t|correct=Some(t)).unwrap();let correct=correct.unwrap();
        let mut wrong=correct;wrong.right.local=0;
        assert_eq!(evaluate(correct,&base_read).unwrap(),Fr::zero());
        assert_eq!(wrong.c[0]+wrong.c[1]*base_read(wrong.left).unwrap(),Fr::zero());
        let c=literal_eq(&r,row_index(owner,0)as u64)*literal_eq(&u,native_index(correct.left)as u64)
            *literal_eq(&v,native_index(correct.right)as u64);
        let bad=literal_eq(&r,row_index(owner,0)as u64)*literal_eq(&u,native_index(wrong.left)as u64)
            *literal_eq(&v,native_index(wrong.right)as u64);
        assert_eq!((c,bad),(Fr::one(),Fr::zero()));faults+=1;
        assert_eq!(faults,483);
    }
    Admitted::new(l,borrowed(owner,&original,&projected,&decoder,&neighbors)).unwrap();
    // Both dense local assignments are dropped on return before next fixture.
    faults
}

fn resource_controls(a:&Authority){assert_eq!(usize::BITS,64);assert_eq!(size_of::<Fr>(),32);
    assert_eq!(size_of::<Gate>(),144);assert_eq!(size_of::<Term>(),152);
    let r=a.resources();assert!(r.core_terms<=172864 && r.core_capacity<=262144);
    assert_eq!(r.serializer_terms,315546);assert!(r.serializer_capacity<=524288);
    assert_eq!(r.boundary_terms,419961);assert!(r.boundary_capacity<=524288);
    assert_eq!(r.certificate_capacity,386);assert!(r.projection_capacity<=4096);
    assert_eq!(size_of::<Mapping>()*384,6144);assert_eq!(size_of::<Alias>()*32,1280);
    assert_eq!(a.certificate().len()*size_of::<Term>(),58672);
    let node=262144usize*208;let refs=131072usize*16;let core=262144usize*152;
    let serializer=524288usize*152;let boundary=524288usize*152;
    let recipes=131072usize*32;let cert=386usize*152;
    let pessimistic=(node+node/2)+(refs+refs/2)+(core+core/2)
        +(serializer+serializer/2)+(boundary+boundary/2)+recipes+cert+32*1024;
    assert!(pessimistic<512*1024*1024,"modeled bound, not RSS");
    assert_eq!(WIDTH*2*size_of::<Fr>(),8388608);
}

#[test]
fn remapped_projection_retires_exact_old_aux_anchors(){
    let authority=Authority::build().expect("one actual public header build");
    resource_controls(&authority);assert_eq!(metadata_faults(&authority),7091);
    let layout=canonical_layout(&authority);source_geometry(&authority,layout);
    assert_eq!(fixture(&authority,layout,844672,0,true),483);
    assert_eq!(fixture(&authority,layout,845823,127,false),0);
    assert_eq!(fixture(&authority,layout,845824,128,false),0);
}
