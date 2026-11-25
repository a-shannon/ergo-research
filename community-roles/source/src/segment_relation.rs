//! Local header-slot relation for the bounded linked-segment experiment.
//! This adapter preserves the original header-hash profile. Parent links are
//! a separate compulsory stage; finite curve membership/PoW/DAA are absent.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use std::ops::Range;
use crate::{gkr::Gate, header_hash, packed::PackedFile, serializer, sparse::{Circuit, Term}};

pub const HEADER_WIDTH: usize = 1 << 20;
pub const DIGEST_OFFSET: usize = 655372;
const CHUNK: usize = 1 << 16;

pub struct Joined {
    pub core4: Circuit,
    pub serializer: serializer::Compiled,
    pub boundary: Circuit,
    pub input: Option<Vec<Fr>>,
    pub parent_wires: [usize; 256],
    pub digest_wires: [usize; 256],
    pub digest_boolean_rows: Range<usize>,
    pub remaining_padding_rows: Range<usize>,
    pub digest_rows: Range<usize>,
}

/// A bounded view of one canonical compression circuit for the global
/// eight-copy header-hash family. Construction verifies the four replicas
/// already present in `Joined::core4`; emission can then replay all eight
/// copies without building a global `EdgeTerm` roster.
pub(crate) struct CoreEdgeSource<'a> {
    terms: &'a [Term],
}

impl<'a> CoreEdgeSource<'a> {
    pub(crate) fn new(joined: &'a Joined) -> Result<Self, String> {
        const SEGMENT_COPIES: usize = 4;
        const CORE_ROW_BITS: usize = 17;
        const CORE_ROWS: usize = 1 << CORE_ROW_BITS;
        const CORE_TERMS: usize = 172_480;
        if joined.core4.input_len != SEGMENT_COPIES * header_hash::CORE_WIDTH
            || joined.core4.row_count != SEGMENT_COPIES * CORE_ROWS
            || joined.core4.terms.len() != SEGMENT_COPIES * CORE_TERMS
        {
            return Err("header core edge source has an invalid four-copy shape".into());
        }
        let terms = &joined.core4.terms[..CORE_TERMS];
        if terms.iter().any(|term| term.row >= CORE_ROWS
            || term.gate.left >= header_hash::CORE_WIDTH
            || term.gate.right >= header_hash::CORE_WIDTH)
        {
            return Err("header core edge template exceeds its local allocation".into());
        }
        for copy in 0..SEGMENT_COPIES {
            let row_offset = copy * CORE_ROWS;
            let wire_offset = copy * header_hash::CORE_WIDTH;
            for (base, actual) in terms.iter().zip(
                &joined.core4.terms[copy * CORE_TERMS..(copy + 1) * CORE_TERMS])
            {
                if actual.row != base.row + row_offset
                    || actual.gate.left != base.gate.left + wire_offset
                    || actual.gate.right != base.gate.right + wire_offset
                    || (actual.gate.c0, actual.gate.c1, actual.gate.c2, actual.gate.c3)
                        != (base.gate.c0, base.gate.c1, base.gate.c2, base.gate.c3)
                {
                    return Err("header core four-copy replicas diverge from their template".into());
                }
            }
        }
        Ok(Self { terms })
    }

    /// Emit all eight compression copies for one header slot. Rows use family
    /// 2 and a 20-bit member allocation; both endpoints remain in that slot.
    pub(crate) fn emit_for_slot(&self, slot: usize,
        sink: &mut dyn FnMut(crate::sparse_stream_roster::EdgeTerm) -> Result<(), String>)
        -> Result<usize, String>
    {
        const SLOT_BITS: usize = 4;
        const BASE_ROW_BITS: usize = 20;
        const FAMILY: usize = 2;
        const CORE_ROW_BITS: usize = 17;
        const CORE_ROWS: usize = 1 << CORE_ROW_BITS;
        if slot >= 1 << SLOT_BITS {
            return Err("header core edge slot is outside the packed history".into());
        }
        let slot_offset = slot.checked_mul(HEADER_WIDTH)
            .ok_or("header core slot offset overflow")?;
        let mut emitted = 0usize;
        for copy in 0..header_hash::CORE_COPIES {
            let row_offset = copy.checked_mul(CORE_ROWS)
                .ok_or("header core row offset overflow")?;
            let wire_offset = slot_offset.checked_add(copy.checked_mul(header_hash::CORE_WIDTH)
                .ok_or("header core wire offset overflow")?)
                .ok_or("header core wire offset overflow")?;
            for base in self.terms {
                let row = row_offset.checked_add(base.row)
                    .ok_or("header core member row overflow")?;
                let family_row = (FAMILY << BASE_ROW_BITS) | row;
                let term = crate::sparse::Term {
                    row,
                    gate: gate(wire_offset + base.gate.left, wire_offset + base.gate.right,
                        [base.gate.c0, base.gate.c1, base.gate.c2, base.gate.c3]),
                };
                sink(crate::sparse_stream_roster::EdgeTerm { source_slot: slot, family_row, term })?;
                emitted = emitted.checked_add(1).ok_or("header core emitted count overflow")?;
            }
        }
        if emitted != header_hash::CORE_COPIES * self.terms.len() {
            return Err("header core edge source did not emit every compression copy".into());
        }
        Ok(emitted)
    }
}

pub fn validate_n(n: usize) -> Result<usize, String> {
    match n { 1 => Ok(0), 2 => Ok(1), 4 => Ok(2),
        _ => Err("segment count must be 1, 2 or 4".into()) }
}

/// Lift a stage's LSB-first input point into the common header-slot matrix.
/// The value is unchanged: inserted Boolean coordinates select an exact bank.
pub fn embed(stage: usize, h: usize, point: &[Fr]) -> Result<Vec<Fr>, String> {
    if h > 2 { return Err("segment header dimension exceeds profile".into()); }
    let (low, fixed): (usize, &[u64]) = match stage {
        0 => (19, &[0]), 1 => (17, &[0,0,1]), 2 => (20, &[]),
        _ => return Err("segment local stage must be 0, 1 or 2".into()),
    };
    if point.len() != low+h { return Err("segment local point dimension mismatch".into()); }
    let mut out = Vec::with_capacity(20+h);
    out.extend_from_slice(&point[..low]);
    out.extend(fixed.iter().copied().map(Fr::from));
    out.extend_from_slice(&point[low..]);
    Ok(out)
}

/// Read a logical stage copy using only the existing bounded packed primitive.
/// Core q=2*header+half; serializer and boundary copies are header indices.
pub fn load_copy(source: &PackedFile, stage: usize, n: usize, copy: usize) -> Result<Vec<Fr>, String> {
    validate_n(n)?;
    if source.input_len() != HEADER_WIDTH*n { return Err("segment packed source dimension mismatch".into()); }
    let (first, chunks) = match stage {
        0 if copy < 2*n => ((copy/2)*16+(copy%2)*4, 4),
        1 if copy < n => (copy*16+8, 2),
        2 if copy < n => (copy*16, 16),
        _ => return Err("segment stage/copy outside profile".into()),
    };
    let mut out = Vec::with_capacity(chunks*CHUNK);
    for chunk in first..first+chunks { out.extend(source.read_copy(CHUNK,chunk)?); }
    Ok(out)
}

fn gate(left: usize, right: usize, coefficients: [Fr;4]) -> Gate {
    Gate {left,right,c0:coefficients[0],c1:coefficients[1],c2:coefficients[2],c3:coefficients[3]}
}

/// Build one reusable local header relation. Private fields affect assignments
/// only. Native encoding/group decoding is not an acceptance shortcut.
pub fn build(fields: Option<&serializer::Fields>) -> Result<Joined, String> {
    let mut old = header_hash::build(fields,[0;32])?;
    let z=Fr::zero();let o=Fr::one();
    if old.core.input_len != CHUNK || old.core.row_count != 1<<17 || old.core.terms.len()!=172480
        || old.boundary.input_len!=HEADER_WIDTH || old.boundary.row_count!=1<<19
        || old.boundary.terms.len()!=419961 || old.boundary_rows.digest.len()!=256
        || old.boundary_rows.global_padding.end!=405784
        || old.boundary_rows.global_padding.len()!=HEADER_WIDTH-DIGEST_OFFSET {
        return Err("header adapter source shape changed".into());
    }
    let digest_rows=old.boundary_rows.digest.clone();
    let padding=old.boundary_rows.global_padding.clone();
    let digest_boolean_rows=padding.start..padding.start+256;
    let remaining_padding_rows=padding.start+256..padding.end;
    let digest_wires=std::array::from_fn(|i|DIGEST_OFFSET+i);
    let parent_wires=std::array::from_fn(|i|header_hash::SERIALIZER_OFFSET+old.serializer.layout.fields.parent_id[i/8][i%8]);
    let first_digest=old.boundary.terms.partition_point(|t|t.row<digest_rows.start);
    let after_digest=old.boundary.terms.partition_point(|t|t.row<digest_rows.end);
    let first_padding=old.boundary.terms.partition_point(|t|t.row<padding.start);
    if after_digest-first_digest!=256*6 || old.boundary.terms.len()-first_padding!=padding.len() {
        return Err("header adapter term grouping changed".into());
    }
    // Validate every replaced term and the five untouched products in its row.
    // This prevents a changed source row from silently becoming another relation.
    for bit in 0..256 {
        let start=first_digest+6*bit;let row=digest_rows.start+bit;
        if old.boundary.terms[start] != (Term {row,gate:gate(0,0,[z,z,z,z])}) {
            return Err("header adapter expected a zero digest constant".into());
        }
        for copy in 0..5 {
            let output=copy*CHUNK+old.compression_layout.output[bit/64][bit%64];
            if old.boundary.terms[start+1+copy] != (Term {row,
                gate:gate(old.selectors[copy],output,[z,z,z,o])}) {
                return Err("header adapter digest selector product changed".into());
            }
        }
        let anchor=first_padding+bit;let row=digest_boolean_rows.start+bit;
        if old.boundary.terms[anchor] != (Term {row,gate:gate(digest_wires[bit],0,[z,o,z,z])}) {
            return Err("header adapter expected a zero padding anchor".into());
        }
    }
    for bit in 0..256 {
        old.boundary.terms[first_digest+6*bit].gate=gate(digest_wires[bit],0,[z,-o,z,z]);
        old.boundary.terms[first_padding+bit].gate=gate(digest_wires[bit],digest_wires[bit],[z,-o,z,o]);
    }
    if let Some(input)=old.input.as_mut() {
        let selected:Vec<_>=old.selectors.iter().enumerate().filter_map(|(i,&w)|input[w].is_one().then_some(i)).collect();
        if selected.len()!=1 || old.selectors.iter().any(|&w|!input[w].is_zero()&&!input[w].is_one()) {
            return Err("header assignment has malformed digest selectors".into());
        }
        for bit in 0..256 {
            let value=input[selected[0]*CHUNK+old.compression_layout.output[bit/64][bit%64]];
            if !value.is_zero()&&!value.is_one() {return Err("header output assignment is non-Boolean".into());}
            input[digest_wires[bit]]=value;
        }
    }
    let mut terms=Vec::with_capacity(4*old.core.terms.len());
    for copy in 0..4 { for term in &old.core.terms {
        let mut shifted=term.clone();shifted.row+=copy*old.core.row_count;
        shifted.gate.left+=copy*CHUNK;shifted.gate.right+=copy*CHUNK;terms.push(shifted);
    }}
    let core4=Circuit {input_len:4*CHUNK,row_count:4*old.core.row_count,terms};
    Ok(Joined {core4,serializer:old.serializer,boundary:old.boundary,input:old.input,
        parent_wires,digest_wires,digest_boolean_rows,remaining_padding_rows,digest_rows})
}

/// Add the complete private serializer relation to the released rows of the
/// header boundary. The matching zero anchors are removed before reuse; all
/// later padding anchors remain. Any larger shared witness that assigns a
/// wire released by this row bank must constrain it in its owning relation.
pub fn attach_serializer_relation(joined: &mut Joined) -> Result<Range<usize>, String> {
    let padding=joined.remaining_padding_rows.clone();
    let source=&joined.serializer.circuit;
    if joined.boundary.input_len!=HEADER_WIDTH || joined.boundary.row_count!=1<<19
        || padding!=(12_836..405_784)
        || source.input_len!=header_hash::SERIALIZER_WIDTH
        || source.row_count!=1<<18 || source.terms.len()!=315_546
        || header_hash::SERIALIZER_OFFSET+source.input_len>DIGEST_OFFSET {
        return Err("canonical serializer adapter source shape changed".into());
    }
    if source.row_count>padding.len()
        || joined.boundary.terms.windows(2).any(|pair|pair[0].row>pair[1].row)
        || source.terms.windows(2).any(|pair|pair[0].row>pair[1].row) {
        return Err("canonical serializer adapter rows are not ordered or do not fit".into());
    }
    let padding_terms=joined.boundary.terms.iter()
        .filter(|term|padding.contains(&term.row)).collect::<Vec<_>>();
    if padding_terms.len()!=padding.len() {
        return Err("canonical serializer adapter padding anchors changed".into());
    }
    let zero=Fr::zero();let one=Fr::one();
    for (offset,term) in padding_terms.iter().enumerate() {
        let wire=DIGEST_OFFSET+256+offset;
        if term.row!=padding.start+offset || term.gate.left!=wire || term.gate.right!=0
            || term.gate.c0!=zero || term.gate.c1!=one
            || term.gate.c2!=zero || term.gate.c3!=zero {
            return Err("canonical serializer adapter expected exact zero anchors".into());
        }
    }

    let used_rows=padding.start..padding.start+source.row_count;
    let first=joined.boundary.terms.partition_point(|term|term.row<used_rows.start);
    let after=joined.boundary.terms.partition_point(|term|term.row<used_rows.end);
    if after-first!=used_rows.len() {
        return Err("canonical serializer adapter row bank is not exclusively padding".into());
    }
    let mut terms=Vec::with_capacity(joined.boundary.terms.len()
        -(after-first)+source.terms.len());
    terms.extend_from_slice(&joined.boundary.terms[..first]);
    for source_term in &source.terms {
        if source_term.row>=source.row_count || source_term.gate.left>=source.input_len
            || source_term.gate.right>=source.input_len {
            return Err("canonical serializer adapter term exceeds its source shape".into());
        }
        let mut term=source_term.clone();
        term.row+=used_rows.start;
        term.gate.left+=header_hash::SERIALIZER_OFFSET;
        term.gate.right+=header_hash::SERIALIZER_OFFSET;
        terms.push(term);
    }
    terms.extend_from_slice(&joined.boundary.terms[after..]);
    #[cfg(test)]
    crate::c425_span_census::replace_source_span_range(first, after, source.terms.len());
    if terms.len()!=joined.boundary.terms.len()-(after-first)+source.terms.len()
        || terms.windows(2).any(|pair|pair[0].row>pair[1].row)
        || terms.iter().any(|term|term.row>=joined.boundary.row_count
            || term.gate.left>=HEADER_WIDTH || term.gate.right>=HEADER_WIDTH) {
        return Err("canonical serializer adapter changed the enclosing relation shape".into());
    }
    joined.boundary.terms=terms;
    joined.remaining_padding_rows=used_rows.end..padding.end;
    Ok(used_rows)
}

/// Translate selected zero-padding wire banks into their exact boundary rows.
/// A shared global relation may omit these rows for the one slot whose owning
/// relation constrains the same wires; all other slots keep the anchors.
pub fn padding_anchor_row_ranges_for_wires(joined:&Joined,
    wire_ranges:&[Range<usize>])->Result<Vec<Range<usize>>,String>{
    let row_base=joined.digest_boolean_rows.end;
    let wire_base=DIGEST_OFFSET+256;
    if row_base>joined.remaining_padding_rows.start
        ||joined.boundary.terms.windows(2).any(|pair|pair[0].row>pair[1].row){
        return Err("padding anchor map has an invalid row base or unordered terms".into());
    }
    let mapped_start=wire_base.checked_add(joined.remaining_padding_rows.start-row_base)
        .ok_or("padding anchor wire offset overflow")?;
    let mapped_end=wire_base.checked_add(joined.remaining_padding_rows.end-row_base)
        .ok_or("padding anchor wire end overflow")?;
    let zero=Fr::zero();let one=Fr::one();
    let mut rows=Vec::with_capacity(wire_ranges.len());
    for wires in wire_ranges{
        if wires.start>=wires.end||wires.start<mapped_start||wires.end>mapped_end{
            return Err("requested wire bank is not in the remaining zero-padding region".into());
        }
        let row_start=row_base.checked_add(wires.start-wire_base)
            .ok_or("padding anchor row offset overflow")?;
        let row_end=row_base.checked_add(wires.end-wire_base)
            .ok_or("padding anchor row end overflow")?;
        if row_start<joined.remaining_padding_rows.start||row_end>joined.remaining_padding_rows.end{
            return Err("requested wire bank maps outside remaining padding rows".into());
        }
        let first=joined.boundary.terms.partition_point(|term|term.row<row_start);
        let after=joined.boundary.terms.partition_point(|term|term.row<row_end);
        if after-first!=row_end-row_start{
            return Err("requested padding bank is not composed only of one anchor per row".into());
        }
        for (offset,term) in joined.boundary.terms[first..after].iter().enumerate(){
            let wire=wires.start+offset;
            if term.row!=row_start+offset||term.gate.left!=wire||term.gate.right!=0
                ||term.gate.c0!=zero||term.gate.c1!=one
                ||term.gate.c2!=zero||term.gate.c3!=zero{
                return Err("requested padding bank contains a noncanonical zero anchor".into());
            }
        }
        rows.push(row_start..row_end);
    }
    Ok(rows)
}

/// Emit one slot's private header-boundary family for the global streaming
/// relation. The caller may omit canonical padding anchors only on a slot
/// whose owning relation constrains the released bank.
pub(crate) fn emit_boundary_edges_for_slot(joined:&Joined,slot:usize,
    released_anchor_rows:&[Range<usize>],
    sink:&mut dyn FnMut(crate::sparse_stream_roster::EdgeTerm)->Result<(),String>)
    ->Result<usize,String>{
    const BASE_ROW_BITS:usize=20;
    const FAMILY:usize=1;
    const SLOT_BITS:usize=4;
    const DAA_CHILD_SLOT:usize=9;
    const A4_ANCHOR_START:usize=348_440;
    const A4_ANCHOR_END:usize=356_632;
    if joined.boundary.input_len!=HEADER_WIDTH||joined.boundary.row_count!=1<<19
        ||slot>=1<<SLOT_BITS||joined.boundary.terms.windows(2).any(|pair|pair[0].row>pair[1].row){
        return Err("private boundary edge source has an invalid slot or circuit shape".into());
    }
    if !released_anchor_rows.is_empty()&&(slot!=DAA_CHILD_SLOT||released_anchor_rows.len()!=1
        ||released_anchor_rows[0].start!=A4_ANCHOR_START||released_anchor_rows[0].end!=A4_ANCHOR_END){
        return Err("the A4 anchor release is restricted to the DAA child slot and mapped range".into());
    }
    let mut expected_skip=0usize;let mut previous_end=None;
    for rows in released_anchor_rows{
        if rows.start>=rows.end||rows.end>joined.boundary.row_count
            ||previous_end.is_some_and(|end|rows.start<end){
            return Err("released boundary rows must be ordered, nonempty and disjoint".into());
        }
        expected_skip=expected_skip.checked_add(rows.len()).ok_or("released row count overflow")?;
        previous_end=Some(rows.end);
    }
    let slot_offset=slot.checked_mul(HEADER_WIDTH).ok_or("boundary slot offset overflow")?;
    let row_base=joined.digest_boolean_rows.end;let wire_base=DIGEST_OFFSET+256;
    let zero=Fr::zero();let one=Fr::one();let mut skipped=0usize;let mut emitted=0usize;
    for term in &joined.boundary.terms{
        if term.row>=joined.boundary.row_count||term.gate.left>=HEADER_WIDTH||term.gate.right>=HEADER_WIDTH{
            return Err("private boundary term exceeds its slot allocation".into());
        }
        if released_anchor_rows.iter().any(|rows|rows.contains(&term.row)){
            let expected_wire=wire_base.checked_add(term.row.checked_sub(row_base)
                .ok_or("released anchor row precedes its padding base")?)
                .ok_or("released anchor wire overflow")?;
            if term.gate.left!=expected_wire||term.gate.right!=0||term.gate.c0!=zero
                ||term.gate.c1!=one||term.gate.c2!=zero||term.gate.c3!=zero{
                return Err("released boundary row is not its canonical zero anchor".into());
            }
            skipped+=1;continue;
        }
        let shifted=crate::sparse::Term{row:term.row,gate:crate::gkr::Gate{
            left:slot_offset+term.gate.left,right:slot_offset+term.gate.right,
            c0:term.gate.c0,c1:term.gate.c1,c2:term.gate.c2,c3:term.gate.c3}};
        sink(crate::sparse_stream_roster::EdgeTerm{source_slot:slot,
            family_row:(FAMILY<<BASE_ROW_BITS)|term.row,term:shifted})?;
        emitted+=1;
    }
    if skipped!=expected_skip||emitted+skipped!=joined.boundary.terms.len(){
        return Err("private boundary edge source did not replay every selected row exactly once".into());
    }
    Ok(skipped)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ergo_header_core::{GroupElement,Header,PowSolution};
    use std::{fs::OpenOptions,io::Write,sync::atomic::{AtomicU64,Ordering}};
    static NEXT:AtomicU64=AtomicU64::new(0);
    fn fields(v:i8,max:bool)->serializer::Fields {
        serializer::Fields {version:v,parent_id:[0x11;32],ad_proofs_root:[0x22;32],transactions_root:[0x33;32],
            state_root:[0x44;33],timestamp:if max {-1}else{1},extension_root:[0x55;32],n_bits:0x00800001,
            height:if max {i32::MAX as u32}else{1},votes:[1,2,3],pk:[0;33],w:[0;33],nonce:[0x80;8],
            payload_len:if max {255}else{0},payload:if max {[0xa5;255]}else{[0;255]}}
    }
    fn native(f:&serializer::Fields)->Vec<u8> {
        let pk=GroupElement::from_bytes(f.pk).unwrap();
        let pow=if f.version==1 {PowSolution::V1 {pk,w:GroupElement::from_bytes(f.w).unwrap(),nonce:f.nonce,
            distance:f.payload[..f.payload_len as usize].to_vec()}} else {PowSolution::V2 {pk,nonce:f.nonce}};
        Header {version:f.version,parent_id:f.parent_id,ad_proofs_root:f.ad_proofs_root,transactions_root:f.transactions_root,
            state_root:f.state_root,timestamp:f.timestamp,extension_root:f.extension_root,n_bits:f.n_bits,
            height:f.height,votes:f.votes,unparsed_bytes:if f.version>4 {f.payload[..f.payload_len as usize].to_vec()}else{vec![]},pow}.encode().unwrap()
    }
    fn residuals(c:&Circuit,input:&[Fr],skip:Option<Range<usize>>)->Vec<Fr> {
        assert_eq!(input.len(),c.input_len);let mut out=vec![Fr::zero();c.row_count];
        for term in &c.terms {if !skip.as_ref().is_some_and(|s|s.contains(&term.row)) {out[term.row]+=term.gate.evaluate(input);}}
        out
    }
    fn failing_rows(c:&Circuit,input:&[Fr])->Vec<usize> {
        residuals(c,input,None).into_iter().enumerate().filter_map(|(i,x)|(!x.is_zero()).then_some(i)).collect()
    }
    fn verify_boundary_edge_stream(joined:&Joined,slot:usize,released:&[std::ops::Range<usize>],
        expected_skipped:usize,expected_emitted:usize)->(bool,bool){
        let mut source_index=0usize;let mut emitted=0usize;let mut a4_anchor_seen=false;
        let mut digest_booleanity_seen=false;let slot_offset=slot*HEADER_WIDTH;
        let skipped=emit_boundary_edges_for_slot(joined,slot,released,&mut |edge|{
            while source_index<joined.boundary.terms.len()
                &&released.iter().any(|rows|rows.contains(&joined.boundary.terms[source_index].row)){
                source_index+=1;
            }
            let source=joined.boundary.terms.get(source_index)
                .ok_or_else(||"boundary stream emitted more terms than its source".to_owned())?;
            assert_eq!(edge.source_slot,slot);
            assert_eq!(edge.family_row,(1usize<<20)|source.row);
            assert_eq!(edge.term.row,source.row);
            assert_eq!(edge.term.gate.left,slot_offset+source.gate.left);
            assert_eq!(edge.term.gate.right,slot_offset+source.gate.right);
            assert_eq!((edge.term.gate.c0,edge.term.gate.c1,edge.term.gate.c2,edge.term.gate.c3),
                (source.gate.c0,source.gate.c1,source.gate.c2,source.gate.c3));
            a4_anchor_seen|=(348_440..356_632).contains(&source.row);
            digest_booleanity_seen|=source.row==joined.digest_boolean_rows.start;
            source_index+=1;emitted+=1;Ok(())
        }).unwrap();
        while source_index<joined.boundary.terms.len()
            &&released.iter().any(|rows|rows.contains(&joined.boundary.terms[source_index].row)){
            source_index+=1;
        }
        assert_eq!(source_index,joined.boundary.terms.len(),"stream must consume the exact source relation");
        assert_eq!(skipped,expected_skipped);
        assert_eq!(emitted,expected_emitted);
        (a4_anchor_seen,digest_booleanity_seen)
    }
    fn independent_eq_table(point:&[Fr])->Vec<Fr>{
        let width=1usize.checked_shl(point.len() as u32).expect("test equality dimension");
        (0..width).map(|index|point.iter().enumerate().fold(Fr::one(),|weight,(bit,coordinate)|
            weight*if (index>>bit)&1==1{*coordinate}else{Fr::one()-coordinate})).collect()
    }
    fn independent_eq_chunks(point:&[Fr])->Vec<Vec<Fr>>{
        point.chunks(8).map(independent_eq_table).collect()
    }
    fn independent_chunked_eq(tables:&[Vec<Fr>],index:usize)->Fr{
        tables.iter().enumerate().fold(Fr::one(),|weight,(chunk,table)|
            weight*table[(index>>(8*chunk))&(table.len()-1)])
    }
    fn independent_diagonal_prefix(r:&[Fr],u:&[Fr],v:&[Fr],end:usize)->Fr{
        assert_eq!(r.len(),u.len());assert_eq!(r.len(),v.len());
        let bits=r.len();let domain=1usize.checked_shl(bits as u32).expect("test prefix dimension");
        assert!(end<=domain);
        let zero=(0..bits).map(|bit|(Fr::one()-r[bit])*(Fr::one()-u[bit])*(Fr::one()-v[bit]))
            .collect::<Vec<_>>();
        let one=(0..bits).map(|bit|r[bit]*u[bit]*v[bit]).collect::<Vec<_>>();
        let mut lower_free=vec![Fr::one();bits+1];
        for bit in 0..bits{lower_free[bit+1]=lower_free[bit]*(zero[bit]+one[bit]);}
        if end==domain{return lower_free[bits];}
        let mut prefix=Fr::one();let mut sum=Fr::zero();
        for bit in (0..bits).rev(){
            if (end>>bit)&1==1{
                sum+=prefix*zero[bit]*lower_free[bit];
                prefix*=one[bit];
            }else{prefix*=zero[bit];}
        }
        sum
    }
    fn factored_core_terminal_coefficients(template:&Circuit,shape:&crate::sparse::Shape,
        r:&[Fr],u:&[Fr],v:&[Fr],slot_bits:usize,active:Range<usize>)->Result<[Fr;4],String>{
        const LOCAL_ROW_BITS:usize=20;
        const LOCAL_INPUT_BITS:usize=20;
        const CORE_ROW_BITS:usize=17;
        const CORE_INPUT_BITS:usize=16;
        let slots=1usize.checked_shl(slot_bits as u32).ok_or("core slot dimension overflow")?;
        if r.len()!=LOCAL_ROW_BITS+slot_bits+2||u.len()!=LOCAL_INPUT_BITS+slot_bits
            ||v.len()!=u.len()||active.start>active.end||active.end>slots{
            return Err("factored core wiring dimensions or slot range changed".into());
        }
        let local=crate::sparse::wiring(template,shape,&r[..CORE_ROW_BITS],
            &u[..CORE_INPUT_BITS],&v[..CORE_INPUT_BITS]).map_err(|error|error.to_string())?;
        let copies=crate::wiring::evaluate_shift(&r[CORE_ROW_BITS..LOCAL_ROW_BITS],
            &u[CORE_INPUT_BITS..CORE_INPUT_BITS+3],&v[CORE_INPUT_BITS..CORE_INPUT_BITS+3],
            0,0,header_hash::CORE_COPIES as u64,0,crate::wiring::RightIndex::SameRow)?;
        let header_slots=crate::wiring::evaluate_shift(&r[LOCAL_ROW_BITS..LOCAL_ROW_BITS+slot_bits],
            &u[LOCAL_INPUT_BITS..],&v[LOCAL_INPUT_BITS..],0,active.start as u64,
            active.end as u64,0,crate::wiring::RightIndex::SameRow)?;
        let family=crate::work_tree_wiring::eq_index(&r[LOCAL_ROW_BITS+slot_bits..],2);
        let zero_padding=(Fr::one()-u[LOCAL_INPUT_BITS-1])*(Fr::one()-v[LOCAL_INPUT_BITS-1]);
        let factor=copies*header_slots*family*zero_padding;
        Ok(std::array::from_fn(|index|local[index]*factor))
    }
    fn explicit_core_terminal_coefficients(source:&CoreEdgeSource<'_>,slots:&[usize],
        r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
        const BASE_ROW_BITS:usize=20;
        const SLOT_BITS:usize=4;
        const CORE_ROW_BITS:usize=17;
        const CORE_INPUT_BITS:usize=16;
        let row_local=independent_eq_table(&r[..CORE_ROW_BITS]);
        let row_copy=independent_eq_table(&r[CORE_ROW_BITS..CORE_ROW_BITS+3]);
        let row_slot=independent_eq_table(&r[BASE_ROW_BITS..BASE_ROW_BITS+SLOT_BITS]);
        let row_family=independent_eq_table(&r[BASE_ROW_BITS+SLOT_BITS..]);
        let left_local=independent_eq_table(&u[..CORE_INPUT_BITS]);
        let left_copy=independent_eq_table(&u[CORE_INPUT_BITS..CORE_INPUT_BITS+3]);
        let left_slot=independent_eq_table(&u[BASE_ROW_BITS..]);
        let right_local=independent_eq_table(&v[..CORE_INPUT_BITS]);
        let right_copy=independent_eq_table(&v[CORE_INPUT_BITS..CORE_INPUT_BITS+3]);
        let right_slot=independent_eq_table(&v[BASE_ROW_BITS..]);
        let zero_padding=(Fr::one()-u[BASE_ROW_BITS-1])*(Fr::one()-v[BASE_ROW_BITS-1]);
        let mut out=[Fr::zero();4];
        for &slot in slots{
            source.emit_for_slot(slot,&mut |edge|{
                let local_row=edge.term.row;
                let copy=local_row>>CORE_ROW_BITS;
                let base_row=local_row&((1<<CORE_ROW_BITS)-1);
                let local_left=edge.term.gate.left-slot*HEADER_WIDTH;
                let local_right=edge.term.gate.right-slot*HEADER_WIDTH;
                let left_copy_index=local_left/header_hash::CORE_WIDTH;
                let right_copy_index=local_right/header_hash::CORE_WIDTH;
                let base_left=local_left%header_hash::CORE_WIDTH;
                let base_right=local_right%header_hash::CORE_WIDTH;
                if edge.source_slot!=slot||edge.family_row>>BASE_ROW_BITS!=2
                    ||edge.family_row&((1<<BASE_ROW_BITS)-1)!=local_row
                    ||copy>=header_hash::CORE_COPIES||left_copy_index!=copy||right_copy_index!=copy{
                    return Err("explicit core edge violates its template/copy mapping".into());
                }
                let global_row=(2usize<<(BASE_ROW_BITS+SLOT_BITS))|(slot<<BASE_ROW_BITS)|local_row;
                let checked_row=crate::sparse_stream_roster::global_edge_row(edge.source_slot,
                    edge.family_row,SLOT_BITS,BASE_ROW_BITS,2,&[17,19,20])?;
                if checked_row!=global_row{return Err("explicit core row map changed".into());}
                let weight=row_local[base_row]*row_copy[copy]*row_slot[slot]*row_family[2]
                    *left_local[base_left]*left_copy[copy]*left_slot[slot]*zero_padding
                    *right_local[base_right]*right_copy[copy]*right_slot[slot];
                for (sum,coefficient) in out.iter_mut().zip([
                    edge.term.gate.c0,edge.term.gate.c1,edge.term.gate.c2,edge.term.gate.c3]){
                    *sum+=weight*coefficient;
                }
                Ok(())
            })?;
        }
        Ok(out)
    }

    #[test]
    #[ignore = "bounded explicit-vs-factored BLAKE wiring differential; no GKR/PCS"]
    fn core_terminal_wiring_factorizes_template_copies_and_active_header_slots(){
        const CORE_TERMS:usize=172_480;
        const HISTORY_HEADERS:usize=1_827_840;
        let joined=build(None).unwrap();
        let source=CoreEdgeSource::new(&joined).unwrap();
        let canonical=header_hash::build(None,[0;32]).unwrap();
        assert_eq!(canonical.core.terms.len(),CORE_TERMS);
        let template=canonical.core;
        let shape=crate::sparse::validate(&template,0).unwrap();
        assert_eq!((shape.row_bits,shape.input_bits),(17,16));
        assert_eq!(template.terms.len(),CORE_TERMS);

        let r=(0..26).map(|i|Fr::from(((i*7+3)%19+2) as u64)).collect::<Vec<_>>();
        let u=(0..24).map(|i|Fr::from(((i*5+4)%23+2) as u64)).collect::<Vec<_>>();
        let v=(0..24).map(|i|Fr::from(((i*3+6)%29+2) as u64)).collect::<Vec<_>>();
        assert!(r.iter().chain(&u).chain(&v).any(|value|value!=&Fr::zero()&&value!=&Fr::one()));
        let cases=vec![
            (vec![9usize],9..10),
            (vec![0usize],0..1),
            (vec![0usize,1],0..2),
            (vec![0usize,1,2,3],0..4),
        ];
        for (slots,active) in cases{
            let expected=explicit_core_terminal_coefficients(&source,&slots,&r,&u,&v).unwrap();
            let actual=factored_core_terminal_coefficients(&template,&shape,&r,&u,&v,4,active.clone()).unwrap();
            assert_eq!(actual,expected,"factored BLAKE wiring for active slots {active:?}");
        }

        // Exercise the exact history dimensions without an 1.8-million-slot
        // witness or a per-slot table. Prefix subtraction isolates the last
        // real header even though the padded domain contains empty slots.
        let large_r=(0..43).map(|i|Fr::from(((i*11+5)%31+2) as u64)).collect::<Vec<_>>();
        let large_u=(0..41).map(|i|Fr::from(((i*13+7)%37+2) as u64)).collect::<Vec<_>>();
        let large_v=(0..41).map(|i|Fr::from(((i*17+9)%41+2) as u64)).collect::<Vec<_>>();
        let slot_r=&large_r[20..41];let slot_u=&large_u[20..];let slot_v=&large_v[20..];
        let slot_domain=1usize<<21;
        for end in [0,1,(1usize<<20)-1,1usize<<20,(1usize<<20)+1,
            HISTORY_HEADERS-1,HISTORY_HEADERS,HISTORY_HEADERS+1,slot_domain-1,slot_domain]{
            let shift=crate::wiring::evaluate_shift(slot_r,slot_u,slot_v,0,0,end as u64,0,
                crate::wiring::RightIndex::SameRow).unwrap();
            assert_eq!(shift,independent_diagonal_prefix(slot_r,slot_u,slot_v,end),
                "21-bit active-prefix boundary {end}");
        }
        let total=factored_core_terminal_coefficients(&template,&shape,&large_r,&large_u,&large_v,
            21,0..HISTORY_HEADERS).unwrap();
        let before_last=factored_core_terminal_coefficients(&template,&shape,&large_r,&large_u,&large_v,
            21,0..HISTORY_HEADERS-1).unwrap();
        let last=factored_core_terminal_coefficients(&template,&shape,&large_r,&large_u,&large_v,
            21,HISTORY_HEADERS-1..HISTORY_HEADERS).unwrap();
        for index in 0..4{assert_eq!(total[index]-before_last[index],last[index],
            "21-bit prefix must add exactly the final active header");}
        let empty=factored_core_terminal_coefficients(&template,&shape,&large_r,&large_u,&large_v,
            21,0..0).unwrap();
        assert_eq!(empty,[Fr::zero();4]);
        println!("factored BLAKE wiring differential: template_terms={CORE_TERMS}, copies=8, toy_cases=slot9/prefix1-2-4, historical_slots={HISTORY_HEADERS}, slot_bits=21, template_visits_per_evaluation={CORE_TERMS}, slot_factor=O(21), gkr=not_run, pcs=not_run, result=pass");
    }

    fn factored_boundary_slot9_coefficients(template:&Circuit,template_shape:&crate::sparse::Shape,
        released:&Circuit,released_shape:&crate::sparse::Shape,r:&[Fr],u:&[Fr],v:&[Fr])
        ->Result<[Fr;4],String>{
        const INPUT_BITS:usize=20;
        const MEMBER_BITS:usize=19;
        const SLOT_BITS:usize=4;
        const SLOT:usize=9;
        if r.len()!=26||u.len()!=INPUT_BITS+SLOT_BITS||v.len()!=u.len()
            ||template.input_len!=1<<INPUT_BITS||template.row_count!=1<<MEMBER_BITS
            ||released.input_len!=template.input_len||released.row_count!=template.row_count{
            return Err("factored private-boundary dimensions changed".into());
        }
        let full=crate::sparse::wiring(template,template_shape,&r[..MEMBER_BITS],
            &u[..INPUT_BITS],&v[..INPUT_BITS]).map_err(|error|error.to_string())?;
        let omitted=crate::sparse::wiring(released,released_shape,&r[..MEMBER_BITS],
            &u[..INPUT_BITS],&v[..INPUT_BITS]).map_err(|error|error.to_string())?;
        let slot=crate::wiring::evaluate_shift(&r[MEMBER_BITS..MEMBER_BITS+SLOT_BITS],
            &u[INPUT_BITS..],&v[INPUT_BITS..],0,SLOT as u64,(SLOT+1) as u64,0,
            crate::wiring::RightIndex::SameRow)?;
        let row_padding=Fr::one()-r[MEMBER_BITS+SLOT_BITS];
        let family=crate::work_tree_wiring::eq_index(&r[MEMBER_BITS+SLOT_BITS+1..],1);
        let factor=slot*row_padding*family;
        Ok(std::array::from_fn(|index|(full[index]-omitted[index])*factor))
    }

    #[test]
    #[ignore = "bounded emitted-vs-factored private-boundary wiring; exact slot 9 only, no GKR/PCS"]
    fn private_boundary_slot9_wiring_factorizes_with_a4_release(){
        const TERMS:usize=473_363;
        const RELEASED_TERMS:usize=8_192;
        const EMITTED_TERMS:usize=465_171;
        const SLOT:usize=9;
        const BASE_ROW_BITS:usize=20;
        const MEMBER_BITS:usize=19;
        const SLOT_BITS:usize=4;
        const FAMILY_BITS:usize=2;
        let mut joined=build(None).unwrap();
        attach_serializer_relation(&mut joined).unwrap();
        assert_eq!(joined.boundary.terms.len(),TERMS);
        let released=padding_anchor_row_ranges_for_wires(&joined,&[991_232..999_424]).unwrap();
        assert_eq!(released,vec![348_440..356_632]);
        let boundary_shape=crate::sparse::validate(&joined.boundary,0).unwrap();
        assert_eq!((boundary_shape.row_bits,boundary_shape.input_bits),(MEMBER_BITS,BASE_ROW_BITS));
        let release_terms=joined.boundary.terms.iter()
            .filter(|term|released.iter().any(|rows|rows.contains(&term.row)))
                .cloned().collect::<Vec<_>>();
        assert_eq!(release_terms.len(),RELEASED_TERMS);
        for term in &release_terms{
            let delta=term.row-released[0].start;
            assert_eq!(term.gate.left,991_232+delta);
            assert_eq!(term.gate.right,0);
            assert_eq!((term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3),
                (Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()));
        }
        let release_circuit=Circuit{input_len:joined.boundary.input_len,
            row_count:joined.boundary.row_count,terms:release_terms};
        let release_shape=crate::sparse::validate(&release_circuit,0).unwrap();
        assert_eq!((release_shape.row_bits,release_shape.input_bits),(MEMBER_BITS,BASE_ROW_BITS));

        let points=[
            ((0..26).map(|i|Fr::from((3+2*i) as u64)).collect::<Vec<_>>(),
             (0..24).map(|i|Fr::from((5+3*i) as u64)).collect::<Vec<_>>(),
             (0..24).map(|i|Fr::from((7+5*i) as u64)).collect::<Vec<_>>()),
            ((0..26).map(|i|Fr::from((7+11*i) as u64)).collect::<Vec<_>>(),
             (0..24).map(|i|Fr::from((9+13*i) as u64)).collect::<Vec<_>>(),
             (0..24).map(|i|Fr::from((11+17*i) as u64)).collect::<Vec<_>>()),
        ];
        for (r,u,v) in points{
            assert!(r.iter().chain(&u).chain(&v).all(|value|!value.is_zero()&&!value.is_one()));
            let r_tables=independent_eq_chunks(&r);
            let u_tables=independent_eq_chunks(&u);
            let v_tables=independent_eq_chunks(&v);
            let mut explicit=[Fr::zero();4];
            let skipped=emit_boundary_edges_for_slot(&joined,SLOT,&released,&mut |edge|{
                let local_row=edge.family_row&((1<<BASE_ROW_BITS)-1);
                if edge.source_slot!=SLOT||edge.family_row>>BASE_ROW_BITS!=1
                    ||local_row!=edge.term.row||edge.term.row>=1<<MEMBER_BITS{
                    return Err("explicit private-boundary source escaped its family or slot".into());
                }
                let global_row=(1usize<<(BASE_ROW_BITS+SLOT_BITS))
                    |(edge.source_slot<<MEMBER_BITS)|local_row;
                let weight=independent_chunked_eq(&r_tables,global_row)
                    *independent_chunked_eq(&u_tables,edge.term.gate.left)
                    *independent_chunked_eq(&v_tables,edge.term.gate.right);
                for (sum,coefficient) in explicit.iter_mut().zip([
                    edge.term.gate.c0,edge.term.gate.c1,edge.term.gate.c2,edge.term.gate.c3]){
                    *sum+=weight*coefficient;
                }
                Ok(())
            }).unwrap();
            assert_eq!(skipped,RELEASED_TERMS);
            let factored=factored_boundary_slot9_coefficients(&joined.boundary,&boundary_shape,
                &release_circuit,&release_shape,&r,&u,&v).unwrap();
            assert_eq!(factored,explicit,"factored boundary wiring at non-Boolean point");

            // These single-fault alternatives must not accidentally preserve the claim.
            let full=crate::sparse::wiring(&joined.boundary,&boundary_shape,&r[..MEMBER_BITS],
                &u[..BASE_ROW_BITS],&v[..BASE_ROW_BITS]).unwrap();
            let omitted=crate::sparse::wiring(&release_circuit,&release_shape,&r[..MEMBER_BITS],
                &u[..BASE_ROW_BITS],&v[..BASE_ROW_BITS]).unwrap();
            let slot=crate::wiring::evaluate_shift(&r[MEMBER_BITS..MEMBER_BITS+SLOT_BITS],
                &u[BASE_ROW_BITS..],&v[BASE_ROW_BITS..],0,SLOT as u64,(SLOT+1) as u64,0,
                crate::wiring::RightIndex::SameRow).unwrap();
            let factor=slot*(Fr::one()-r[MEMBER_BITS+SLOT_BITS])
                *crate::work_tree_wiring::eq_index(&r[MEMBER_BITS+SLOT_BITS+1..],1);
            let without_release=std::array::from_fn::<_,4,_>(|index|full[index]*factor);
            let wrong_release_sign=std::array::from_fn::<_,4,_>(|index|(full[index]+omitted[index])*factor);
            assert_ne!(without_release,explicit,"omitting the A4 release changes wiring");
            assert_ne!(wrong_release_sign,explicit,"reversing the A4 release changes wiring");
        }
        println!("private boundary wiring differential: terms={TERMS}, released_anchors={RELEASED_TERMS}, emitted={EMITTED_TERMS}, slot={SLOT}, non_boolean_points=2, gkr=not_run, pcs=not_run, result=pass");
    }

    #[test]
    fn core_edge_source_streams_all_eight_canonical_compression_copies() {
        const SLOT: usize = 9;
        const CORE_ROWS: usize = 1 << 17;
        const CORE_TERMS: usize = 172_480;
        const BASE_ROW_BITS: usize = 20;
        let mut joined = build(Some(&fields(4, false))).unwrap();
        let canonical = header_hash::build(None, [0; 32]).unwrap();
        assert_eq!(canonical.core.terms.len(), CORE_TERMS);
        let source = CoreEdgeSource::new(&joined).unwrap();
        let mut seen = 0usize;
        let emitted = source.emit_for_slot(SLOT, &mut |edge| {
            let copy = seen / CORE_TERMS;
            let index = seen % CORE_TERMS;
            let base = &canonical.core.terms[index];
            let local_row = copy * CORE_ROWS + base.row;
            let wire_offset = SLOT * HEADER_WIDTH + copy * header_hash::CORE_WIDTH;
            assert_eq!(edge.source_slot, SLOT);
            assert_eq!(edge.family_row, (2 << BASE_ROW_BITS) | local_row);
            assert_eq!(edge.term.row, local_row);
            assert_eq!(edge.term.gate.left, wire_offset + base.gate.left);
            assert_eq!(edge.term.gate.right, wire_offset + base.gate.right);
            assert_eq!((edge.term.gate.c0, edge.term.gate.c1,
                edge.term.gate.c2, edge.term.gate.c3),
                (base.gate.c0, base.gate.c1, base.gate.c2, base.gate.c3));
            assert_eq!(edge.family_row >> BASE_ROW_BITS, 2);
            assert!(edge.term.gate.left < 16 * HEADER_WIDTH
                && edge.term.gate.right < 16 * HEADER_WIDTH);
            assert!(crate::sparse_stream_roster::global_edge_row(edge.source_slot,
                edge.family_row, 4, BASE_ROW_BITS, 2, &[17, 19, 20]).is_ok());
            seen += 1;
            Ok(())
        }).unwrap();
        assert_eq!(emitted, header_hash::CORE_COPIES * CORE_TERMS);
        assert_eq!(seen, emitted);

        let mut wrong_slot_emitted = 0;
        assert!(source.emit_for_slot(16, &mut |_| {
            wrong_slot_emitted += 1;
            Ok(())
        }).is_err());
        assert_eq!(wrong_slot_emitted, 0, "invalid slots must fail before emission");
        drop(source);

        joined.core4.terms[CORE_TERMS + 7].gate.left += 1;
        assert!(CoreEdgeSource::new(&joined).is_err(),
            "a mutated stored replica must not seed the eight-copy stream");
    }
    fn components(j:&Joined) {
        let input=j.input.as_ref().unwrap();assert!(input.iter().all(|x|x.is_zero()||x.is_one()));
        for half in input[..header_hash::SERIALIZER_OFFSET].chunks_exact(4*CHUNK) {assert!(failing_rows(&j.core4,half).is_empty());}
        assert!(failing_rows(&j.serializer.circuit,&input[header_hash::SERIALIZER_OFFSET..header_hash::AUX_OFFSET]).is_empty());
        assert!(failing_rows(&j.boundary,input).is_empty());
    }
    #[test]
    fn adapter_preserves_rows_and_changes_only_declared_terms() {
        let old=header_hash::build(None,[0;32]).unwrap();let new=build(None).unwrap();
        assert!(new.input.is_none());assert!(new.serializer.input.is_none());
        assert_eq!((new.core4.input_len,new.core4.row_count,new.core4.terms.len()),(1<<18,1<<19,689920));
        assert_eq!((new.boundary.row_count,new.boundary.terms.len()),(1<<19,419961));
        assert_eq!(new.remaining_padding_rows.end,405784);
        let mut altered=0;
        for (a,b) in old.boundary.terms.iter().zip(&new.boundary.terms) {
            assert_eq!(a.row,b.row);
            if a!=b {altered+=1;assert!(new.digest_rows.contains(&a.row)||new.digest_boolean_rows.contains(&a.row));}
        }
        assert_eq!(altered,512);
        for copy in 0..4 { for (original,shifted) in old.core.terms.iter().zip(&new.core4.terms[copy*old.core.terms.len()..]) {
            let mut expected=original.clone();expected.row+=copy*old.core.row_count;
            expected.gate.left+=copy*CHUNK;expected.gate.right+=copy*CHUNK;assert_eq!(&expected,shifted);
        }}
        for bit in 0..256 {assert_eq!(new.parent_wires[bit],header_hash::SERIALIZER_OFFSET+old.serializer.layout.fields.parent_id[bit/8][bit%8]);}
    }
    #[test]
    fn private_digest_boundary_proves_full_serializer_for_multiple_lengths() {
        let without_serializer=build(None).unwrap();
        let mut fixed=build(None).unwrap();
        let serializer_rows=attach_serializer_relation(&mut fixed).unwrap();
        assert_eq!(serializer_rows,12_836..274_980);
        assert_eq!(fixed.remaining_padding_rows,274_980..405_784);
        assert_eq!((fixed.boundary.input_len,fixed.boundary.row_count,fixed.boundary.terms.len()),
            (HEADER_WIDTH,1<<19,473_363));
        assert_eq!(fixed.digest_boolean_rows,without_serializer.digest_boolean_rows);
        assert!(fixed.boundary.terms.iter().any(|term|term.row==fixed.digest_boolean_rows.start),
            "private digest Booleanity row must survive serializer composition");
        let mut observed_lengths=Vec::new();

        for f in [fields(4,false),fields(1,true)] {
            let instance=build(Some(&f)).unwrap();
            assert_eq!(instance.core4,fixed.core4);
            assert_eq!(instance.serializer.circuit,fixed.serializer.circuit);
            let input=instance.input.unwrap();
            let serialized_length=instance.serializer.layout.length.iter().enumerate()
                .map(|(bit,&wire)|if input[header_hash::SERIALIZER_OFFSET+wire].is_one(){1usize<<bit}else{0})
                .sum::<usize>();
            assert_eq!(serialized_length,native(&f).len());
            observed_lengths.push(serialized_length);
            assert!(residuals(&instance.serializer.circuit,
                &input[header_hash::SERIALIZER_OFFSET..header_hash::AUX_OFFSET],None)
                .iter().all(Zero::is_zero));
            assert!(failing_rows(&fixed.boundary,&input).is_empty(),
                "fixed private-length/digest relation must accept native length {serialized_length}");

            // The old boundary sees serialized bytes and the BLAKE transcript,
            // but not their consistency with this private source field.
            let field_bit=instance.serializer.layout.fields.timestamp[0];
            assert!(!instance.serializer.layout.bytes.iter().any(|byte|byte.contains(&field_bit))
                && !instance.serializer.layout.length.contains(&field_bit),
                "mutant field must be distinct from serialized bytes and public-length wires");
            let field_wire=header_hash::SERIALIZER_OFFSET+field_bit;
            let mut inconsistent=input.clone();
            inconsistent[field_wire]=if inconsistent[field_wire].is_zero(){Fr::one()}else{Fr::zero()};
            assert!(failing_rows(&without_serializer.boundary,&inconsistent).is_empty(),
                "the isolated source-field mutant must expose the missing serializer relation");
            let failures=failing_rows(&fixed.boundary,&inconsistent);
            assert!(!failures.is_empty()&&failures.iter().all(|row|serializer_rows.contains(row)),
                "full serializer relation must reject only within its assigned row bank");
            assert!(residuals(&fixed.boundary,&inconsistent,Some(serializer_rows.clone()))
                .iter().all(Zero::is_zero),
                "omitting the serializer rows must admit the isolated source-field mutant");
        }
        assert_ne!(observed_lengths[0],observed_lengths[1],
            "fixtures must exercise distinct private canonical lengths");
    }
    #[test]
    fn child_daa_bank_maps_only_its_remaining_padding_anchors(){
        let mut joined=build(None).unwrap();
        attach_serializer_relation(&mut joined).unwrap();
        let released=padding_anchor_row_ranges_for_wires(&joined,&[991_232..999_424]).unwrap();
        assert_eq!(released,vec![348_440..356_632]);
        assert_eq!(released[0].len(),8_192);

        let first=joined.boundary.terms.partition_point(|term|term.row<released[0].start);
        let after=joined.boundary.terms.partition_point(|term|term.row<released[0].end);
        assert_eq!(after-first,released[0].len());
        for (offset,term) in joined.boundary.terms[first..after].iter().enumerate(){
            let wire=991_232+offset;
            assert_eq!(term.row,348_440+offset);
            assert_eq!((term.gate.left,term.gate.right),(wire,0));
            assert_eq!((term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3),
                (Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()));
            assert_eq!(term.gate.c0+term.gate.c1*Fr::one(),Fr::one(),
                "the original anchor rejects a nonzero DAA-owned wire");
        }
        assert!(joined.boundary.terms.iter().any(|term|term.row==released[0].start-1
            &&term.gate.left==991_231),"the preceding wire anchor must remain");
        assert!(joined.boundary.terms.iter().any(|term|term.row==released[0].end
            &&term.gate.left==999_424),"the following wire anchor must remain");
        assert!(joined.boundary.terms.iter().any(|term|term.row==joined.digest_boolean_rows.start),
            "private digest Booleanity must remain outside the released bank");
        assert!(padding_anchor_row_ranges_for_wires(&joined,&[819_200..851_968]).is_err(),
            "a bank already occupied by the serializer row overlay is not a remaining padding anchor");
        assert!(padding_anchor_row_ranges_for_wires(&joined,&[991_232..1_048_577]).is_err(),
            "the release map must reject wires outside the header input");
    }
    #[test]
    fn private_boundary_releases_a4_anchors_only_for_the_child_slot(){
        let mut template=build(None).unwrap();attach_serializer_relation(&mut template).unwrap();
        let released=padding_anchor_row_ranges_for_wires(&template,&[991_232..999_424]).unwrap();
        assert_eq!(released,vec![348_440..356_632]);
        let (ordinary_a4,digest_on_slot0)=verify_boundary_edge_stream(&template,0,&[],0,473_363);
        assert!(ordinary_a4,
            "the same rows remain constrained on ordinary header slots");
        let mut wrong_slot_emissions=0usize;
        assert_eq!(emit_boundary_edges_for_slot(&template,0,&released,&mut |_|{
            wrong_slot_emissions+=1;Ok(())
        }).unwrap_err(),"the A4 anchor release is restricted to the DAA child slot and mapped range");
        assert_eq!(wrong_slot_emissions,0,"an invalid release request must fail before emitting edges");
        let (child_a4,digest_on_child)=verify_boundary_edge_stream(&template,9,&released,8_192,465_171);
        assert!(!child_a4,"only the child's A4 anchors may be omitted");
        assert!(digest_on_slot0&&digest_on_child,
            "child digest Booleanity must survive bank release");

        {
            let mut short=build(Some(&fields(4,false))).unwrap();attach_serializer_relation(&mut short).unwrap();
            let short_input=short.input.as_ref().unwrap();
            assert_eq!(native(&fields(4,false)).len(),213);
            assert!(failing_rows(&short.boundary,short_input).is_empty(),
                "private serializer boundary must accept native length 213 on slot 0");
        }

        let mut child=build(Some(&fields(1,true))).unwrap();attach_serializer_relation(&mut child).unwrap();
        let child_input=child.input.as_ref().unwrap();
        assert_eq!(native(&fields(1,true)).len(),514);
        assert!(failing_rows(&template.boundary,child_input).is_empty(),
            "private serializer boundary must accept native length 514 on slot 9");
        assert!(residuals(&template.boundary,child_input,Some(released[0].clone()))
            .iter().all(Zero::is_zero),
            "the streamed child relation must retain every constraint except its mapped anchors");

        let mut changed=child_input.clone();changed[991_232]=Fr::one();
        assert_eq!(failing_rows(&child.boundary,&changed),vec![released[0].start],
            "the unreleased relation must expose the exact conflicting A4 anchor");
        assert!(residuals(&template.boundary,&changed,Some(released[0].clone()))
            .iter().all(Zero::is_zero),
            "the child boundary may release only the A4 zero anchor");
    }
    #[test]
    fn private_native_digests_and_topology_match_at_two_lengths() {
        let public=build(None).unwrap();
        for f in [fields(4,false),fields(1,true)] {
            let j=build(Some(&f)).unwrap();assert_eq!(j.core4,public.core4);assert_eq!(j.boundary,public.boundary);
            assert_eq!(j.serializer.circuit,public.serializer.circuit);components(&j);
            let raw=native(&f);if f.version==1 {assert_eq!(raw.len(),514);}
            let expected=ergo_header_core::blake2b256(&raw);let input=j.input.as_ref().unwrap();
            for bit in 0..256 {assert_eq!(input[j.digest_wires[bit]],Fr::from(((expected[bit/8]>>(bit%8))&1) as u64));}
            assert!(j.digest_wires.iter().any(|&w|input[w].is_one()));
        }
    }
    #[test]
    fn digest_boolean_and_remaining_padding_fail_at_exact_rows() {
        let j=build(Some(&fields(4,false))).unwrap();let original=j.input.as_ref().unwrap();
        let mut changed=original.clone();changed[j.digest_wires[0]]=Fr::one()-changed[j.digest_wires[0]];
        assert_eq!(failing_rows(&j.boundary,&changed),vec![j.digest_rows.start]);
        assert!(residuals(&j.boundary,&changed,Some(j.digest_rows.start..j.digest_rows.start+1)).iter().all(|x|x.is_zero()));
        // Boundary-only Booleanity falsifier: keep its digest equation exact by
        // changing the selected output too. This is not a valid core witness.
        let zero_digest_term=j.boundary.terms.iter().find(|t|t.row==j.digest_rows.start && !t.gate.c3.is_zero()
            && original[t.gate.left].is_one()).unwrap();
        let mut changed=original.clone();changed[j.digest_wires[0]]=Fr::from(2u64);changed[zero_digest_term.gate.right]=Fr::from(2u64);
        assert_eq!(failing_rows(&j.boundary,&changed),vec![j.digest_boolean_rows.start]);
        assert!(residuals(&j.boundary,&changed,Some(j.digest_boolean_rows.start..j.digest_boolean_rows.start+1)).iter().all(|x|x.is_zero()));
        for (wire,row) in [(DIGEST_OFFSET+256,j.remaining_padding_rows.start),(HEADER_WIDTH-1,j.remaining_padding_rows.end-1)] {
            let mut changed=original.clone();changed[wire]=Fr::one();assert_eq!(failing_rows(&j.boundary,&changed),vec![row]);
            assert!(residuals(&j.boundary,&changed,Some(row..row+1)).iter().all(|x|x.is_zero()));
        }
    }
    #[test]
    fn count_and_embedding_admission_are_exact() {
        for n in [1usize,2,4] {let h=validate_n(n).unwrap();assert_eq!(1<<h,n);
            for (stage,low,insert) in [(0,19,vec![Fr::zero()]),(1,17,vec![Fr::zero(),Fr::zero(),Fr::one()]),(2,20,vec![])] {
                let p:Vec<_>=(0..low+h).map(|i|Fr::from((i+2) as u64)).collect();let lifted=embed(stage,h,&p).unwrap();
                let expected:Vec<_>=p[..low].iter().chain(insert.iter()).chain(p[low..].iter()).copied().collect();
                assert_eq!(lifted,expected);assert_eq!(lifted.len(),20+h);
                assert!(embed(stage,h,&p[..p.len()-1]).is_err());
            }
        }
        for n in [0,3,5,8,usize::MAX] {assert!(validate_n(n).is_err());}
        assert!(embed(3,0,&[]).is_err());assert!(embed(0,3,&[]).is_err());
    }
    #[test]
    fn packed_loader_covers_distinct_headers_and_halfbanks() {
        for n in [1usize,2,4] {
            let bytes:Vec<u8>=(0..HEADER_WIDTH*n/8).map(|i|((i/(CHUNK/8)) as u8).wrapping_mul(37)
                .wrapping_add((i%(CHUNK/8)) as u8).rotate_left(1)).collect();
            let path=std::env::temp_dir().join(format!("segment-loader-{}-{}.bits",std::process::id(),NEXT.fetch_add(1,Ordering::Relaxed)));
            let mut file=OpenOptions::new().write(true).create_new(true).open(&path).unwrap();file.write_all(&bytes).unwrap();drop(file);
            let source=PackedFile::open(&path,20+validate_n(n).unwrap()).unwrap();
            for stage in 0..3 {for copy in 0..if stage==0 {2*n}else{n} {
                let got=load_copy(&source,stage,n,copy).unwrap();
                // Independent global-bit addresses, not the production chunk loop.
                let (header,offset,width)=match stage {0=>(copy/2,(copy%2)*(1<<18),1<<18),
                    1=>(copy,header_hash::SERIALIZER_OFFSET,1<<17),_=>(copy,0,HEADER_WIDTH)};
                assert_eq!(got.len(),width);
                for (i,value) in got.iter().enumerate() {let bit=header*HEADER_WIDTH+offset+i;
                    assert_eq!(*value,Fr::from(((bytes[bit/8]>>(bit%8))&1) as u64));}
            }}
            for (stage,copy) in [(0,2*n),(1,n),(2,n),(3,0)] {assert!(load_copy(&source,stage,n,copy).is_err());}
            assert!(load_copy(&source,0,8,0).is_err());
            assert!(load_copy(&source,0,if n==1 {2}else{1},0).is_err());
            drop(source);std::fs::remove_file(path).unwrap();
        }
    }
}
