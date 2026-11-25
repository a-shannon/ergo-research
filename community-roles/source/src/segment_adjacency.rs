//! Bounded parent/digest adjacency, with a compact verifier-owned descriptor.
//! Header coordinates are the low 20 bits; row coordinates are the low 9 bits.
//! This relation checks links and endpoints, not hashes, header validity or PoW.
//! Its returned input claim MUST be opened under the caller's common commitment.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::{self, Gate, GkrError, GkrProof, InputClaim, LayerProof},
    packed::PackedFile, transcript::Transcript, wiring::{evaluate_shift, RightIndex}};

const HEADER_BITS: usize = 20;
const ROW_BITS: usize = 9;
const ID_BITS: usize = 256;
const LINE_CHUNK_BITS: usize = 16;

/// Observed reader calls and vector lengths, not allocation capacities or RSS.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StreamStats {
    pub chunk_reads: u64,
    pub chunk_fields_max: usize,
    pub transition_fields_max: usize,
}

enum StreamPhase<'a> {
    Left { parents: &'a [[u8;32]] },
    Right { u: &'a [Fr], a: Fr, endpoint: Fr },
}

fn read_stream_chunk(load: &mut impl FnMut(usize)->Result<Vec<Fr>,String>,
    chunk: usize, width: usize, stats: &mut StreamStats) -> Result<Vec<Fr>,String>
{
    stats.chunk_reads += 1;
    let values=load(chunk)?;
    stats.chunk_fields_max=stats.chunk_fields_max.max(values.len());
    if values.len()!=width {return Err("adjacency streamed chunk width mismatch".into());}
    if values.iter().any(|x|!x.is_zero()&&!x.is_one()) {
        return Err("adjacency streamed source is non-Boolean".into());
    }
    Ok(values)
}

fn accept_stream_round(polynomial: Vec<Fr>, claim: &mut Fr,
    rounds: &mut Vec<Vec<Fr>>, transcript: &mut Transcript) -> Result<Fr,String>
{
    if polynomial[0]+gkr::eval_polynomial(&polynomial,Fr::one())!=*claim {
        return Err(GkrError::SumcheckIdentity.to_string());
    }
    gkr::append_polynomial(transcript,b"gkr-sumcheck-polynomial",&polynomial);
    let challenge=transcript.challenge_scalar(b"gkr-sumcheck-challenge");
    *claim=gkr::eval_polynomial(&polynomial,challenge);rounds.push(polynomial);
    Ok(challenge)
}

#[derive(Clone, Debug)]
pub struct Relation {
    n: usize,
    header_bits: usize,
    parent_wires: [usize; ID_BITS],
    digest_wires: [usize; ID_BITS],
    parent: [u8; 32],
    tip: [u8; 32],
}

fn eq_index(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |weight, (bit, value)| {
        weight * if (index >> bit) & 1 == 1 { *value } else { Fr::one() - value }
    })
}
fn id_bit(id: &[u8; 32], bit: usize) -> Fr { Fr::from(((id[bit / 8] >> (bit % 8)) & 1) as u64) }

impl Relation {
    /// Both maps address local Boolean bit wires in one fixed header bank.
    /// The caller derives these maps from its own serializer/hash topology.
    pub fn new(n: usize, parent_wires: [usize; 256], digest_wires: [usize; 256],
        parent: [u8; 32], tip: [u8; 32]) -> Result<Self, String> {
        if !matches!(n, 1 | 2 | 4) { return Err("adjacency supports exactly N=1,2,4".into()); }
        let mut indices = parent_wires.iter().chain(&digest_wires).copied().collect::<Vec<_>>();
        if indices.iter().any(|i| *i >= 1usize << HEADER_BITS) { return Err("adjacency wire outside header bank".into()); }
        indices.sort_unstable();
        if indices.windows(2).any(|pair| pair[0] == pair[1]) { return Err("adjacency bit maps must be distinct".into()); }
        Ok(Self { n, header_bits: HEADER_BITS, parent_wires, digest_wires, parent, tip })
    }
    /// Fixed 512-bit local projection for the two compact-link roles. The
    /// public full-header constructor above retains its original descriptor.
    pub(crate) fn new_compact(n:usize,parent:[u8;32],tip:[u8;32])->Result<Self,String> {
        if !matches!(n,1|2|4) {return Err("compact adjacency supports exactly N=1,2,4".into());}
        Ok(Self {n,header_bits:9,parent_wires:std::array::from_fn(|j|j),
            digest_wires:std::array::from_fn(|j|256+j),parent,tip})
    }
    pub fn input_log(&self) -> usize { self.header_bits + self.n.trailing_zeros() as usize }
    pub fn input_len(&self) -> usize { 1usize << self.input_log() }
    pub fn row_count(&self) -> usize { self.n << ROW_BITS }

    /// Bind once in the caller's all-stage preamble, and again locally when the
    /// adjacency protocol begins. No expanded gate list enters this transcript.
    pub fn bind(&self, transcript: &mut Transcript) {
        transcript.append_bytes(b"adjacency-profile", b"header-parent-digest-shift-one-v1");
        transcript.append_u64(b"adjacency-headers", self.n as u64);
        transcript.append_u64(b"adjacency-header-bits", self.header_bits as u64);
        transcript.append_u64(b"adjacency-row-bits", ROW_BITS as u64);
        transcript.append_bytes(b"adjacency-preceding-parent", &self.parent);
        transcript.append_bytes(b"adjacency-final-tip", &self.tip);
        for (parent, digest) in self.parent_wires.iter().zip(&self.digest_wires) {
            transcript.append_u64(b"adjacency-parent-bit-wire", *parent as u64);
            transcript.append_u64(b"adjacency-digest-bit-wire", *digest as u64);
        }
    }

    // Producer enumeration only. The verifier never invokes this function.
    fn for_each_gate(&self, mut visit: impl FnMut(usize, Gate)) {
        let zero = Fr::zero(); let one = Fr::one();
        for j in 0..ID_BITS {
            visit(j, Gate { left: self.parent_wires[j], right: 0,
                c0: -id_bit(&self.parent,j), c1: one, c2: zero, c3: zero });
        }
        for i in 1..self.n {
            for j in 0..ID_BITS {
                visit((i << ROW_BITS) + j, Gate {
                    left: ((i-1) << self.header_bits) + self.digest_wires[j],
                    right: (i << self.header_bits) + self.parent_wires[j],
                    c0: zero, c1: one, c2: -one, c3: zero });
            }
        }
        for j in 0..ID_BITS {
            visit(((self.n-1) << ROW_BITS) + ID_BITS + j, Gate {
                left: ((self.n-1) << self.header_bits) + self.digest_wires[j], right: 0,
                c0: -id_bit(&self.tip,j), c1: one, c2: zero, c3: zero });
        }
    }

    /// Crate-owned composite relations re-emit these gates in their own
    /// common witness. This does not create a separate proof or PCS claim.
    pub(crate) fn visit_terms(&self, sink: impl FnMut(usize, Gate)) {
        self.for_each_gate(sink);
    }

    pub(crate) fn wiring_coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr])
        -> Result<[Fr; 4], GkrError>
    {
        self.coefficients(r, u, v)
    }

    pub fn residuals(&self, input: &[Fr]) -> Result<Vec<Fr>, String> {
        if input.len() != self.input_len() { return Err("adjacency input width mismatch".into()); }
        let mut rows = vec![Fr::zero(); self.row_count()];
        self.for_each_gate(|row, gate| { rows[row] += gate.evaluate(input); }); Ok(rows)
    }

    /// O(256*(20+9)+log N) field work and no N-sized tables or gate arrays.
    fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr;4], GkrError> {
        let h = self.n.trailing_zeros() as usize;
        if r.len() != ROW_BITS+h || u.len() != self.input_log() || v.len() != self.input_log() {
            return Err(GkrError::PointDimension);
        }
        let (r_low,r_high) = r.split_at(ROW_BITS);
        let (u_low,u_high) = u.split_at(self.header_bits);
        let (v_low,v_high) = v.split_at(self.header_bits);
        let link_factor = evaluate_shift(r_high,u_high,v_high,1,1,self.n as u64,0,RightIndex::SameRow)
            .map_err(|_| GkrError::PointDimension)?;
        let mut link_local = Fr::zero();
        let mut first = [Fr::zero();2];
        let mut last = [Fr::zero();2];
        for j in 0..ID_BITS {
            let row_weight = eq_index(r_low,j);
            link_local += row_weight * eq_index(u_low,self.digest_wires[j]) * eq_index(v_low,self.parent_wires[j]);
            // The constant and linear term share this exact row AND left wire.
            let first_weight = row_weight * eq_index(u_low,self.parent_wires[j]);
            first[0] -= first_weight * id_bit(&self.parent,j); first[1] += first_weight;
            let last_weight = eq_index(r_low,ID_BITS+j) * eq_index(u_low,self.digest_wires[j]);
            last[0] -= last_weight * id_bit(&self.tip,j); last[1] += last_weight;
        }
        // Endpoint gates have right=0 globally, including all header-index bits.
        let right_zero = eq_index(v,0);
        let first_factor = eq_index(r_high,0) * eq_index(u_high,0) * right_zero;
        let last_factor = eq_index(r_high,self.n-1) * eq_index(u_high,self.n-1) * right_zero;
        let link = link_local * link_factor;
        Ok([first[0]*first_factor+last[0]*last_factor,
            link+first[1]*first_factor+last[1]*last_factor, -link, Fr::zero()])
    }

    pub fn prove(&self, input: &[Fr], transcript: &mut Transcript) -> Result<(GkrProof,InputClaim),String> {
        if self.residuals(input)?.iter().any(|value| !value.is_zero()) {
            return Err("nonzero adjacency residual".into());
        }
        self.bind(transcript);
        let r = gkr::output_point(self.row_count(),transcript);
        gkr::append_usize(transcript,b"gkr-layer-index",0);
        let row_weights = gkr::eq_weights(&r); // Producer only; at most 2048 fields.
        let mut claim = Fr::zero(); let mut rounds = Vec::new();
        let mut a = vec![Fr::zero();input.len()]; let mut b = vec![Fr::zero();input.len()];
        self.for_each_gate(|row,gate| {
            let weight = row_weights[row];
            a[gate.left] += weight * (gate.c1 + gate.c3*input[gate.right]);
            b[gate.left] += weight * (gate.c0 + gate.c2*input[gate.right]);
        });
        // prove_phase consumes a/b and releases its one input copy on return.
        // Including the caller input, at most four global Fr arrays are live.
        let (u,left_value) = gkr::prove_phase(a,b,input,&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
        let mut c = vec![Fr::zero();input.len()]; let mut d = vec![Fr::zero();input.len()];
        self.for_each_gate(|row,gate| {
            let weight = row_weights[row] * eq_index(&u,gate.left);
            c[gate.right] += weight * (gate.c2+gate.c3*left_value);
            d[gate.right] += weight * (gate.c0+gate.c1*left_value);
        });
        let (v,right_value) = gkr::prove_phase(c,d,input,&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
        let coefficients = self.coefficients(&r,&u,&v).map_err(|e|e.to_string())?;
        if coefficients[0]+coefficients[1]*left_value+coefficients[2]*right_value
            +coefficients[3]*left_value*right_value != claim { return Err(GkrError::TerminalExpression.to_string()); }
        let line_coefficients = chunked_line(input,&u,&v,LINE_CHUNK_BITS)?;
        if line_coefficients[0] != left_value || gkr::eval_polynomial(&line_coefficients,Fr::one()) != right_value {
            return Err(GkrError::LineEndpoints.to_string());
        }
        transcript.append_scalar(b"gkr-left-value",&left_value); transcript.append_scalar(b"gkr-right-value",&right_value);
        gkr::append_polynomial(transcript,b"gkr-line-polynomial",&line_coefficients);
        let challenge = transcript.challenge_scalar(b"gkr-line-challenge");
        let point = gkr::line_point(&u,&v,challenge);
        let value = gkr::eval_polynomial(&line_coefficients,challenge);
        Ok((GkrProof {layers:vec![LayerProof {rounds,left_value,right_value,line_coefficients}]},InputClaim {point,value}))
    }

    /// Exact dense-proof counterpart for an immutable Boolean packed source.
    /// Arbitrary field-valued dense witnesses are outside this entry point.
    pub fn prove_streamed_boolean(&self, source: &PackedFile, transcript: &mut Transcript)
        -> Result<(GkrProof,InputClaim,StreamStats),String>
    {
        if source.input_len()!=self.input_len() {return Err("adjacency packed source dimension mismatch".into());}
        self.prove_streamed_reader(LINE_CHUNK_BITS,|chunk|source.read_copy(1<<LINE_CHUNK_BITS,chunk),transcript)
    }

    /// Read one fixed compact bank from each immutable global header. This is
    /// crate-private so callers cannot supply unbound maps or a guessed bank.
    pub(crate) fn prove_compact_streamed_boolean(&self,source:&PackedFile,bank:usize,
        transcript:&mut Transcript)->Result<(GkrProof,InputClaim,StreamStats),String> {
        if self.header_bits!=9 || !matches!(self.n,1|2|4)
            || self.parent_wires!=std::array::from_fn(|j|j)
            || self.digest_wires!=std::array::from_fn(|j|256+j)
            || !matches!(bank,1552|1554) {
            return Err("compact adjacency descriptor or bank invalid".into());
        }
        if source.input_len()!=self.n* (1usize<<HEADER_BITS) {
            return Err("compact adjacency packed source dimension mismatch".into());
        }
        self.prove_streamed_reader(9,|header|source.read_copy(512,header*2048+bank),transcript)
    }

    // Fixed production entries select 2^16 (full) or 2^9 (compact) chunks;
    // other widths and injected readers are private test seams. The reader
    // must be immutable: production retains the PackedFile lock.
    fn prove_streamed_reader(&self, chunk_bits: usize,
        mut load: impl FnMut(usize)->Result<Vec<Fr>,String>, transcript: &mut Transcript)
        -> Result<(GkrProof,InputClaim,StreamStats),String>
    {
        if chunk_bits>LINE_CHUNK_BITS || chunk_bits>self.input_log() {
            return Err("adjacency streamed chunk dimension invalid".into());
        }
        let width=1usize<<chunk_bits;let chunks=self.input_len()/width;
        let mut stats=StreamStats::default();
        let mut parents=vec![[0u8;32];self.n];let mut digests=vec![[0u8;32];self.n];
        // Full validation precedes any binding append or challenge, including
        // bits outside all gates. The cache is 64 bytes/header, not 512 Fr.
        for chunk in 0..chunks {
            let x=read_stream_chunk(&mut load,chunk,width,&mut stats)?;
            let first=chunk*width;let end=first+width;
            for header in first>>self.header_bits..=((end-1)>>self.header_bits) {
                for j in 0..ID_BITS {
                    for (wire,cache) in [(self.parent_wires[j],&mut parents),(self.digest_wires[j],&mut digests)] {
                        let index=(header<<self.header_bits)+wire;
                        if index>=first && index<end && x[index-first].is_one() {cache[header][j/8]|=1<<(j%8);}
                    }
                }
            }
        }
        if parents[0]!=self.parent || digests[self.n-1]!=self.tip
            || (1..self.n).any(|i|digests[i-1]!=parents[i]) {
            return Err("nonzero adjacency residual".into());
        }
        drop(digests);
        self.bind(transcript);let r=gkr::output_point(self.row_count(),transcript);
        gkr::append_usize(transcript,b"gkr-layer-index",0);
        // 512 fixed local weights plus N high weights, never 512*N weights.
        let row_low=gkr::eq_weights(&r[..ROW_BITS]);let row_high=gkr::eq_weights(&r[ROW_BITS..]);
        let mut claim=Fr::zero();let mut rounds=Vec::new();
        let (u,left_value)=self.stream_phase(chunk_bits,&StreamPhase::Left {parents:&parents},
            &row_low,&row_high,&mut load,&mut stats,&mut claim,&mut rounds,transcript)?;
        drop(parents);
        let mut endpoint=Fr::zero();
        for j in 0..ID_BITS {
            endpoint+=row_low[j]*row_high[0]*eq_index(&u,self.parent_wires[j])*(left_value-id_bit(&self.parent,j));
            endpoint+=row_low[ID_BITS+j]*row_high[self.n-1]
                *eq_index(&u,((self.n-1)<<self.header_bits)+self.digest_wires[j])*(left_value-id_bit(&self.tip,j));
        }
        let (v,right_value)=self.stream_phase(chunk_bits,&StreamPhase::Right {u:&u,a:left_value,endpoint},
            &row_low,&row_high,&mut load,&mut stats,&mut claim,&mut rounds,transcript)?;
        drop(row_low);drop(row_high);
        let coefficients=self.coefficients(&r,&u,&v).map_err(|e|e.to_string())?;
        if coefficients[0]+coefficients[1]*left_value+coefficients[2]*right_value
            +coefficients[3]*left_value*right_value!=claim {return Err(GkrError::TerminalExpression.to_string());}
        let line_coefficients=self.stream_line(chunk_bits,&u,&v,&mut load,&mut stats)?;
        if line_coefficients[0]!=left_value || gkr::eval_polynomial(&line_coefficients,Fr::one())!=right_value {
            return Err(GkrError::LineEndpoints.to_string());
        }
        transcript.append_scalar(b"gkr-left-value",&left_value);transcript.append_scalar(b"gkr-right-value",&right_value);
        gkr::append_polynomial(transcript,b"gkr-line-polynomial",&line_coefficients);
        let challenge=transcript.challenge_scalar(b"gkr-line-challenge");
        let point=gkr::line_point(&u,&v,challenge);let value=gkr::eval_polynomial(&line_coefficients,challenge);
        Ok((GkrProof {layers:vec![LayerProof {rounds,left_value,right_value,line_coefficients}]},InputClaim {point,value},stats))
    }

    // Reconstruct exactly the prefix-folded coefficient arrays for one chunk.
    // Local lists are filtered: <=512 integer index checks per chunk/header,
    // but each contributing gate is evaluated only once per complete pass.
    fn stream_vectors(&self, chunk: usize, width: usize, prefix: &[Fr], phase: &StreamPhase,
        row_low: &[Fr], row_high: &[Fr]) -> (Vec<Fr>,Vec<Fr>)
    {
        let first=chunk*width;let end=first+width;let k=prefix.len();
        let mut a=vec![Fr::zero();width>>k];let mut b=vec![Fr::zero();width>>k];
        let mut add=|wire:usize,ca:Fr,cb:Fr| {
            let factor=eq_index(prefix,wire);let index=(wire-first)>>k;
            a[index]+=factor*ca;b[index]+=factor*cb;
        };
        match phase {
            StreamPhase::Left {parents} => {
                for header in first>>self.header_bits..=((end-1)>>self.header_bits) {
                    for j in 0..ID_BITS {
                        if header==0 && self.parent_wires[j]>=first && self.parent_wires[j]<end {
                            let weight=row_low[j]*row_high[0];
                            add(self.parent_wires[j],weight,-weight*id_bit(&self.parent,j));
                        }
                        let wire=(header<<self.header_bits)+self.digest_wires[j];
                        if wire>=first && wire<end {
                            let (weight,rhs)=if header+1<self.n {
                                (row_low[j]*row_high[header+1],id_bit(&parents[header+1],j))
                            } else {(row_low[ID_BITS+j]*row_high[header],id_bit(&self.tip,j))};
                            add(wire,weight,-weight*rhs);
                        }
                    }
                }
            },
            StreamPhase::Right {u,a:value,endpoint} => {
                if first==0 {add(0,Fr::zero(),*endpoint);}
                for header in (first>>self.header_bits).max(1)..=((end-1)>>self.header_bits) {
                    for j in 0..ID_BITS {
                        let wire=(header<<self.header_bits)+self.parent_wires[j];
                        if wire>=first && wire<end {
                            let weight=row_low[j]*row_high[header]
                                *eq_index(u,((header-1)<<self.header_bits)+self.digest_wires[j]);
                            add(wire,-weight,weight*(*value));
                        }
                    }
                }
            },
        }
        (a,b)
    }

    #[allow(clippy::too_many_arguments)]
    fn stream_phase(&self, chunk_bits: usize, phase: &StreamPhase, row_low: &[Fr], row_high: &[Fr],
        load: &mut impl FnMut(usize)->Result<Vec<Fr>,String>, stats: &mut StreamStats,
        claim: &mut Fr, rounds: &mut Vec<Vec<Fr>>, transcript: &mut Transcript) -> Result<(Vec<Fr>,Fr),String>
    {
        let width=1usize<<chunk_bits;let chunks=self.input_len()/width;let mut point=Vec::new();
        for _ in 0..chunk_bits {
            let mut polynomial=vec![Fr::zero();3];
            for chunk in 0..chunks {
                let mut x=read_stream_chunk(load,chunk,width,stats)?;
                for coordinate in &point {gkr::fold(&mut x,*coordinate);}
                let (a,b)=self.stream_vectors(chunk,width,&point,phase,row_low,row_high);
                for (total,local) in polynomial.iter_mut().zip(gkr::quadratic_message(&a,&b,&x)) {*total+=local;}
            }
            point.push(accept_stream_round(polynomial,claim,rounds,transcript)?);
        }
        let mut a=vec![Fr::zero();chunks];let mut b=vec![Fr::zero();chunks];let mut x=vec![Fr::zero();chunks];
        stats.transition_fields_max=stats.transition_fields_max.max(a.len()+b.len()+x.len());
        for chunk in 0..chunks {
            let mut local=read_stream_chunk(load,chunk,width,stats)?;
            for coordinate in &point {gkr::fold(&mut local,*coordinate);}
            let (aa,bb)=self.stream_vectors(chunk,width,&point,phase,row_low,row_high);
            a[chunk]=aa[0];b[chunk]=bb[0];x[chunk]=local[0];
        }
        while x.len()>1 {
            let polynomial=gkr::quadratic_message(&a,&b,&x);
            let challenge=accept_stream_round(polynomial,claim,rounds,transcript)?;
            gkr::fold(&mut a,challenge);gkr::fold(&mut b,challenge);gkr::fold(&mut x,challenge);point.push(challenge);
        }
        Ok((point,x[0]))
    }

    fn stream_line(&self, chunk_bits: usize, u: &[Fr], v: &[Fr],
        load: &mut impl FnMut(usize)->Result<Vec<Fr>,String>, stats: &mut StreamStats) -> Result<Vec<Fr>,String>
    {
        let width=1usize<<chunk_bits;let mut result=vec![Fr::zero();self.input_log()+1];
        for chunk in 0..self.input_len()/width {
            let x=read_stream_chunk(load,chunk,width,stats)?;
            let local=gkr::line_polynomial(&x,&u[..chunk_bits],&v[..chunk_bits]);
            let high=selector_line(chunk,&u[chunk_bits..],&v[chunk_bits..]);
            for (out,value) in result.iter_mut().zip(multiply(&local,&high)) {*out+=value;}
        }
        Ok(result)
    }

    pub fn verify(&self, proof: &GkrProof, transcript: &mut Transcript) -> Result<InputClaim,String> {
        gkr::verify_with_wiring(&[self.input_log()],self.row_count(),proof,transcript,
            |t|self.bind(t), |_layer,r,u,v|self.coefficients(r,u,v)).map_err(|e|e.to_string())
    }
    pub fn decode_proof(&self, bytes: &[u8]) -> Result<GkrProof,String> {
        gkr::decode_dimensions(&[self.input_log()],bytes)
    }
}

fn multiply(a: &[Fr], b: &[Fr]) -> Vec<Fr> {
    let mut out = vec![Fr::zero();a.len()+b.len()-1];
    for (i,x) in a.iter().enumerate() { for (j,y) in b.iter().enumerate() {out[i+j] += *x*y;} } out
}
fn selector_line(index: usize, u: &[Fr], v: &[Fr]) -> Vec<Fr> {
    let mut out = vec![Fr::one()];
    for (bit,(a,b)) in u.iter().zip(v).enumerate() {
        let linear = if (index>>bit)&1 == 1 {[*a,*b-a]} else {[Fr::one()-a,*a-b]};
        out = multiply(&out,&linear);
    } out
}
// Sum local MLE line polynomials times their high-coordinate selector lines.
// One <=2^16-entry chunk is processed at a time. The local helper temporarily
// retains old and new folding tables, so its scratch remains O(chunk).
fn chunked_line(input: &[Fr], u: &[Fr], v: &[Fr], chunk_bits: usize) -> Result<Vec<Fr>,String> {
    if u.len()!=v.len() || u.len()>HEADER_BITS+2 || input.len()!=1usize<<u.len() || chunk_bits>LINE_CHUNK_BITS {
        return Err("adjacency line dimensions invalid".into());
    }
    let low = chunk_bits.min(u.len()); let width = 1usize<<low;
    let mut result = vec![Fr::zero();u.len()+1];
    for (index,chunk) in input.chunks_exact(width).enumerate() {
        let local = gkr::line_polynomial(chunk,&u[..low],&v[..low]);
        let high = selector_line(index,&u[low..],&v[low..]);
        let contribution = multiply(&local,&high);
        for (out,value) in result.iter_mut().zip(contribution) {*out += value;}
    } Ok(result)
}

#[cfg(test)]
pub(crate) mod linear_for_test {
    use super::*;
    use crate::header_adjacency_layout::linear_for_test::Descriptor;
    use std::time::Instant;

    pub(crate) const LIMIT:usize=512*1024*1024;
    pub(crate) const PHASES:[&str;4]=["validation","u","v","line"];
    #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    pub(crate) enum Native5Side {U,V}
    #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    pub(crate) enum Native5Progress {
        ValidationComplete,Round{side:Native5Side,completed:usize},LineComplete,ProducerComplete,
    }
    const FIXED_BOUND:usize=65536;
    fn add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or("linear capacity sum overflow".into())}
    fn mul(a:usize,b:usize)->Result<usize,String>{a.checked_mul(b).ok_or("linear capacity product overflow".into())}
    fn cap<T>(v:&Vec<T>)->Result<usize,String>{mul(v.capacity(),std::mem::size_of::<T>())}
    fn round_cap(rounds:&Vec<Vec<Fr>>)->Result<usize,String>{
        rounds.iter().try_fold(cap(rounds)?,|sum,v|add(sum,cap(v)?))
    }
    #[derive(Clone,Debug,Default,serde::Serialize)]
    pub(crate) struct Stats {
        pub(crate) phase_ns:[u64;4],pub(crate) read_calls:[u64;4],pub(crate) reconstructed_fields:[u64;4],
        pub(crate) direct_vector_capacity_peak_bytes:[usize;4],
        pub(crate) helper_scratch_bound_peak_bytes:[usize;4],pub(crate) combined_bound_peak_bytes:[usize;4],
        pub(crate) preflight_bound_bytes:usize,pub(crate) scoped_limit_bytes:usize,
        pub(crate) retained_capacity_bytes:usize,pub(crate) fixed_typed_bound_bytes:usize,
        pub(crate) high_fold_coordinates:[usize;2],pub(crate) initial_padding_chunks:usize,
        pub(crate) line_input_fields:usize,pub(crate) helper_bounds_measured:bool,
    }
    /// Separately charged, allocation-free support inventory. Existing Stats
    /// remains the complete-scan report contract.
    #[derive(Clone,Debug,serde::Serialize)]
    pub(crate) struct SupportStats {
        pub(crate) chunks_per_owner:usize,
        pub(crate) parent_chunk_mask:u16,pub(crate) digest_chunk_mask:u16,
        pub(crate) support_chunks:[usize;2],
        pub(crate) low_round_read_calls:[u64;2],pub(crate) low_round_skipped_chunks:[u64;2],
        pub(crate) control_capacity_bytes:usize,
    }
    #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    #[repr(u8)]
    enum SupportFault {None,OmitGenesis,OmitTip,OmitGlobalZero,WrongChunk,AOnly,ZeroSkippedHighX}
    struct SupportControl {stats:SupportStats,fault:SupportFault}
    impl SupportControl {
        fn capacity_bound()->Result<usize,String>{
            // Original plus construction/return move overlap; returned census;
            // three optional selector borrows in inner body, phase and low helper.
            add(add(mul(2,std::mem::size_of::<Self>())?,std::mem::size_of::<SupportStats>())?,
                mul(3,std::mem::size_of::<Option<&mut Self>>())?)
        }
        fn new(d:&Descriptor<'_>,fault:SupportFault)->Result<Self,String>{
            if d.local_input()!=20||d.local_row()!=9||d.chunk_bits()!=16||d.ids()!=256{
                return Err("support requires canonical20/9/16 geometry".into());
            }
            let chunks_per_owner=1usize<<(d.local_input()-d.chunk_bits());
            let mask=|wires:&[usize]|->Result<u16,String>{
                wires.iter().try_fold(0u16,|m,wire|{
                    if *wire>=1usize<<d.local_input(){return Err("support local wire bound".into());}
                    let bit=1u16.checked_shl((*wire>>d.chunk_bits()) as u32).ok_or("support mask overflow")?;
                    Ok(m|bit)
                })
            };
            let parent_chunk_mask=mask(d.parent())?;let digest_chunk_mask=mask(d.digest())?;
            if chunks_per_owner!=16||parent_chunk_mask!=256||digest_chunk_mask!=1024{
                return Err("support canonical parent/digest chunks changed".into());
            }
            let support_chunks=[add(mul(d.active(),digest_chunk_mask.count_ones() as usize)?,
                parent_chunk_mask.count_ones() as usize)?,
                add(1,mul(d.active()-1,parent_chunk_mask.count_ones() as usize)?)?];
            Ok(Self{fault,stats:SupportStats{chunks_per_owner,parent_chunk_mask,digest_chunk_mask,support_chunks,
                low_round_read_calls:[0;2],low_round_skipped_chunks:[0;2],control_capacity_bytes:Self::capacity_bound()?}})
        }
        fn canonical(&self,d:&Descriptor<'_>,phase:usize,chunk:usize)->bool{
            let owner=chunk/self.stats.chunks_per_owner;let bit=1u16<<(chunk%self.stats.chunks_per_owner);
            match phase {
                1=>(owner==0&&self.stats.parent_chunk_mask&bit!=0)
                    ||(owner<d.active()&&self.stats.digest_chunk_mask&bit!=0),
                2=>chunk==0||(owner>0&&owner<d.active()&&self.stats.parent_chunk_mask&bit!=0),
                _=>false,
            }
        }
        fn contains(&self,d:&Descriptor<'_>,phase:usize,chunk:usize)->bool{
            if self.fault==SupportFault::WrongChunk{
                let owner=chunk/self.stats.chunks_per_owner;let bit=1u16<<(chunk%self.stats.chunks_per_owner);
                let wrong_parent=self.stats.parent_chunk_mask<<1;
                return match phase{
                    1=>(owner==0&&wrong_parent&bit!=0)||(owner<d.active()&&self.stats.digest_chunk_mask&bit!=0),
                    2=>chunk==0||(owner>0&&owner<d.active()&&wrong_parent&bit!=0),_=>false,
                };
            }
            if !self.canonical(d,phase,chunk){return false;}
            let owner=chunk/self.stats.chunks_per_owner;let bit=1u16<<(chunk%self.stats.chunks_per_owner);
            match self.fault {
                SupportFault::OmitGenesis if phase==1&&owner==0&&self.stats.parent_chunk_mask&bit!=0=>false,
                SupportFault::OmitTip if phase==1&&owner+1==d.active()&&self.stats.digest_chunk_mask&bit!=0=>false,
                SupportFault::OmitGlobalZero|SupportFault::AOnly if phase==2&&chunk==0=>false,
                _=>true,
            }
        }
        fn skipped(&mut self,phase:usize)->Result<(),String>{
            self.stats.low_round_skipped_chunks[phase-1]=self.stats.low_round_skipped_chunks[phase-1]
                .checked_add(1).ok_or("support skipped census overflow")?;Ok(())
        }
        fn read(&mut self,phase:usize)->Result<(),String>{
            self.stats.low_round_read_calls[phase-1]=self.stats.low_round_read_calls[phase-1]
                .checked_add(1).ok_or("support read census overflow")?;Ok(())
        }
        fn complete(&self,d:&Descriptor<'_>)->Result<(),String>{
            let chunks=d.input_len()/(1usize<<d.chunk_bits());
            for side in 0..2{
                let reads=mul(d.chunk_bits(),self.stats.support_chunks[side])? as u64;
                let skipped=mul(d.chunk_bits(),chunks-self.stats.support_chunks[side])? as u64;
                if self.stats.low_round_read_calls[side]!=reads||self.stats.low_round_skipped_chunks[side]!=skipped{
                    return Err("support complete structural census".into());
                }
            }Ok(())
        }
    }
    pub(crate) fn preflight_for_test(d:&Descriptor<'_>,retained:usize)->Result<Stats,String>{
        d.validate(d.input_len(),d.chunk_bits())?;
        Ok(Audit::new(d,retained)?.stats)
    }
    pub(crate) fn historical50_resource_controls_for_test()->Result<(),String>{
        let layout=crate::header_adjacency_layout::HeaderAdjacencyLayout::compile(3,2,[0;32],[0;32])?;
        let d=layout.linear_descriptor_for_test()?;let control=SupportControl::new(&d,SupportFault::None)?;
        if control.stats.control_capacity_bytes!=256{return Err("historical50 support charge ABI".into());}
        let base=Audit::new(&d,256)?.stats.preflight_bound_bytes;
        let retained=LIMIT.checked_sub(base).and_then(|n|n.checked_add(256)).ok_or("historical50 Audit boundary")?;
        let mut audit=Audit::new(&d,retained)?;
        if audit.stats.preflight_bound_bytes!=LIMIT||Audit::new(&d,retained+1).err().as_deref()!=Some("linear scoped preflight exceeds512MiB"){
            return Err("historical50 Audit preflight attribution".into());}
        let room=LIMIT.checked_sub(retained+FIXED_BOUND).ok_or("historical50 Audit room")?;
        audit.observe(0,room,0)?;
        if audit.observe(0,room+1,0).err().as_deref()!=Some("linear actual vector inventory exceeds preflight"){
            return Err("historical50 Audit actual inventory attribution".into());}
        let mut golden=SupportControl::new(&d,SupportFault::None)?;
        let chunks=d.input_len()/(1usize<<d.chunk_bits());
        for side in 0..2{golden.stats.low_round_read_calls[side]=(d.chunk_bits()*golden.stats.support_chunks[side]) as u64;
            golden.stats.low_round_skipped_chunks[side]=(d.chunk_bits()*(chunks-golden.stats.support_chunks[side])) as u64;}
        golden.complete(&d)?;
        for side in 0..2{for skipped in [false,true]{let mut bad=SupportControl::new(&d,SupportFault::None)?;bad.stats=golden.stats.clone();
            if skipped{bad.stats.low_round_skipped_chunks[side]+=1;}else{bad.stats.low_round_read_calls[side]+=1;}
            if bad.complete(&d).err().as_deref()!=Some("support complete structural census"){return Err("historical50 isolated support census fault".into());}}}
        Ok(())
    }
    /// Caller declarations for this diagnostic trial, not measured RSS or an
    /// operating-system cap. Ordinary/H50 policy remains fixed at LIMIT.
    #[derive(Clone,Copy,Debug)]
    pub(crate) struct H21Role5Budget {
        pub(crate) limit_bytes:usize,pub(crate) caller_context_bytes:usize,pub(crate) unmeasured_bytes:usize,
    }
    #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    pub(crate) struct H21Role5ResourcePlan {
        pub(crate) chunks:usize,pub(crate) chunk_bytes:usize,pub(crate) parent_cache_bytes:usize,
        pub(crate) owner_weights_bytes:usize,pub(crate) high_vectors_bytes:usize,
        pub(crate) phase_bounds:[usize;4],pub(crate) known_peak_bytes:usize,pub(crate) required_bytes:usize,
        pub(crate) control_bytes:usize,
    }
    pub(crate) fn h21_role5_resource_preflight(d:&Descriptor<'_>,source_len:usize,budget:H21Role5Budget)
        ->Result<H21Role5ResourcePlan,String>{
        d.validate_h21(source_len)?;
        if std::mem::size_of::<Fr>()!=32{return Err("H21 role5 field ABI".into());}
        let width=1usize<<16;let chunks=source_len/width;
        if chunks!=1usize<<25{return Err("H21 role5 chunk census".into());}
        let chunk_bytes=mul(width,32)?;
        let parent_cache_bytes=mul(d.active(),d.ids().div_ceil(8))?;
        let owner_weights_bytes=mul(add(1usize<<d.local_row(),d.padded())?,32)?;
        let high_vectors_bytes=mul(mul(3,chunks)?,32)?;
        let small=add(FIXED_BOUND,mul(d.input_log()+1,1024)?)?;
        let loader=add(width.div_ceil(8),1024)?;
        let validation=add(add(mul(parent_cache_bytes,2)?,chunk_bytes)?,add(loader,small)?)?;
        let weight_build=add(parent_cache_bytes,add(mul(owner_weights_bytes,4)?,add(1024,small)?)?)?;
        let low=add(add(parent_cache_bytes,owner_weights_bytes)?,add(mul(chunk_bytes,3)?,add(loader,small)?)?)?;
        // Three 2^25-field high arrays coexist with one folded chunk. U
        // still owns the parent cache; it is dropped before V starts.
        let high_u=add(add(add(parent_cache_bytes,owner_weights_bytes)?,high_vectors_bytes)?,
            add(chunk_bytes,add(64,add(loader,small)?)?)?)?;
        let high_v=add(add(owner_weights_bytes,high_vectors_bytes)?,add(chunk_bytes,add(64,add(loader,small)?)?)?)?;
        let line=add(add(mul(chunk_bytes,3)?,4096)?.max(crate::sparse_stream_roster::h21_table_line::scratch_bytes()?),small)?;
        let phase_bounds=[validation,weight_build.max(low).max(high_u),high_v.max(low-parent_cache_bytes),line];
        let known_peak_bytes=*phase_bounds.iter().max().ok_or("H21 role5 empty phase plan")?;
        if budget.caller_context_bytes==0||budget.unmeasured_bytes==0 {
            return Err("H21 role5 caller/unmeasured reservations must be explicit".into());
        }
        let control_bytes=SupportControl::capacity_bound()?;
        let required_bytes=add(known_peak_bytes,add(add(budget.caller_context_bytes,budget.unmeasured_bytes)?,control_bytes)?)?;
        if budget.limit_bytes<required_bytes{return Err("H21 role5 declared budget below phase reservation".into());}
        Ok(H21Role5ResourcePlan {chunks,chunk_bytes,parent_cache_bytes,owner_weights_bytes,high_vectors_bytes,
            phase_bounds,known_peak_bytes,required_bytes,control_bytes})
    }

    struct Audit{stats:Stats,width:usize}
    impl Audit {
        fn new(d:&Descriptor<'_>,retained:usize)->Result<Self,String>{
            let width=1usize<<d.chunk_bits();let chunks=d.input_len()/width;
            let cache=mul(mul(d.active(),d.ids().div_ceil(8))?,2)?;
            let weights=mul(add(1usize<<d.local_row(),d.padded())?,32)?;
            // Deliberately reserve simultaneous stage vectors, proof/point
            // growth and unchanged helper scratch before any allocation/read.
            let work=mul(add(mul(width,5)?,mul(chunks,3)?)?,32)?;
            let proof=mul(d.input_log()+1,1024)?;
            let preflight=add(add(add(add(add(retained,FIXED_BOUND)?,cache)?,weights)?,work)?,proof)?;
            if preflight>LIMIT{return Err("linear scoped preflight exceeds512MiB".into());}
            Ok(Self{width,stats:Stats{preflight_bound_bytes:preflight,scoped_limit_bytes:LIMIT,
                retained_capacity_bytes:retained,fixed_typed_bound_bytes:FIXED_BOUND,..Default::default()}})
        }
        fn h21(d:&Descriptor<'_>,budget:H21Role5Budget)->Result<Self,String>{
            let plan=h21_role5_resource_preflight(d,d.input_len(),budget)?;
            let retained=add(add(budget.caller_context_bytes,budget.unmeasured_bytes)?,plan.control_bytes)?;
            Ok(Self {width:1<<16,stats:Stats {preflight_bound_bytes:plan.required_bytes,
                scoped_limit_bytes:budget.limit_bytes,retained_capacity_bytes:retained,
                fixed_typed_bound_bytes:FIXED_BOUND,..Default::default()}})
        }
        fn observe(&mut self,phase:usize,direct:usize,helper:usize)->Result<(),String>{
            let total=add(add(add(direct,helper)?,self.stats.retained_capacity_bytes)?,FIXED_BOUND)?;
            if total>self.stats.preflight_bound_bytes||total>self.stats.scoped_limit_bytes{return Err("linear actual vector inventory exceeds preflight".into());}
            self.stats.direct_vector_capacity_peak_bytes[phase]=self.stats.direct_vector_capacity_peak_bytes[phase].max(direct);
            self.stats.helper_scratch_bound_peak_bytes[phase]=self.stats.helper_scratch_bound_peak_bytes[phase].max(helper);
            self.stats.combined_bound_peak_bytes[phase]=self.stats.combined_bound_peak_bytes[phase].max(total);Ok(())
        }
        fn read(&mut self,phase:usize,chunk:usize,base:usize,
            load:&mut impl FnMut(usize)->Result<Vec<Fr>,String>)->Result<Vec<Fr>,String>{
            let x=load(chunk)?;
            if x.len()!=self.width||x.capacity()>self.width{return Err("linear short/oversized chunk".into());}
            // The unchanged packed reader has a packed-byte buffer in addition
            // to its returned Fr vector. This is a derived bound, not a sample.
            self.observe(phase,add(base,cap(&x)?)?,add(self.width.div_ceil(8),1024)?)?;
            self.stats.read_calls[phase]=self.stats.read_calls[phase].checked_add(1).ok_or("linear read census overflow")?;
            self.stats.reconstructed_fields[phase]=self.stats.reconstructed_fields[phase]
                .checked_add(x.len() as u64).ok_or("linear reconstruction census overflow")?;
            if x.iter().any(|v|!v.is_zero()&&!v.is_one()){return Err("linear non-Boolean chunk".into());}Ok(x)
        }
    }
    enum Phase<'a>{Left(&'a[u8]),Right{u:&'a Vec<Fr>,value:Fr,endpoint:Fr}}
    fn cached(bytes:&[u8],stride:usize,owner:usize,bit:usize)->Fr{
        Fr::from(((bytes[owner*stride+bit/8]>>(bit%8))&1) as u64)
    }
    fn vectors(d:&Descriptor<'_>,chunk:usize,width:usize,prefix:&[Fr],phase:&Phase<'_>,
        low:&[Fr],high:&[Fr])->(Vec<Fr>,Vec<Fr>){
        let first=chunk*width;let end=first+width;let k=prefix.len();
        let mut a=vec![Fr::zero();width>>k];let mut b=vec![Fr::zero();width>>k];
        let mut inject=|wire:usize,ca:Fr,cb:Fr|{let weight=eq_index(prefix,wire);let at=(wire-first)>>k;
            a[at]+=weight*ca;b[at]+=weight*cb;};
        match phase {
            Phase::Left(parents)=>{
                for owner in first>>d.local_input()..=((end-1)>>d.local_input()).min(d.active()-1){
                    for j in 0..d.ids(){
                        if owner==0&&d.parent()[j]>=first&&d.parent()[j]<end{
                            let w=low[j]*high[0];inject(d.parent()[j],w,-w*d.start_bit(j));
                        }
                        let wire=(owner<<d.local_input())+d.digest()[j];
                        if wire>=first&&wire<end{
                            let (w,rhs)=if owner+1<d.active(){(low[j]*high[owner+1],cached(parents,d.ids().div_ceil(8),owner+1,j))}
                                else{(low[d.ids()+j]*high[owner],d.tip_bit(j))};
                            inject(wire,w,-w*rhs);
                        }
                    }
                }
            },
            Phase::Right{u,value,endpoint}=>{
                if first==0{inject(0,Fr::zero(),*endpoint);}
                for owner in (first>>d.local_input()).max(1)..=((end-1)>>d.local_input()).min(d.active()-1){
                    for j in 0..d.ids(){let wire=(owner<<d.local_input())+d.parent()[j];
                        if wire>=first&&wire<end{let w=low[j]*high[owner]*eq_index(u,((owner-1)<<d.local_input())+d.digest()[j]);
                            inject(wire,-w,w*(*value));}
                    }
                }
            },
        }(a,b)
    }
    fn low_message(d:&Descriptor<'_>,kind:&Phase<'_>,index:usize,low:&Vec<Fr>,high:&Vec<Fr>,cache_bytes:usize,
        load:&mut impl FnMut(usize)->Result<Vec<Fr>,String>,audit:&mut Audit,
        rounds:&Vec<Vec<Fr>>,point:&Vec<Fr>,mut support:Option<&mut SupportControl>)->Result<Vec<Fr>,String>{
        let width=audit.width;let chunks=d.input_len()/width;
        let borrowed=match kind{Phase::Right{u,..}=>cap(u)?,_=>0};
        let mut polynomial=vec![Fr::zero();3];
        for chunk in 0..chunks{
            if let Some(control)=support.as_deref_mut(){
                if !control.contains(d,index,chunk){control.skipped(index)?;continue;}
            }
            let base=add(add(add(add(add(cache_bytes,cap(low)?)?,cap(high)?)?,round_cap(rounds)?)?,cap(point)?)?,add(borrowed,cap(&polynomial)?)?)?;
            let mut x=audit.read(index,chunk,base,load)?;
            if let Some(control)=support.as_deref_mut(){control.read(index)?;}
            for coordinate in point{gkr::fold(&mut x,*coordinate);}
            let (a,b)=vectors(d,chunk,width,point,kind,low,high);
            audit.observe(index,add(add(add(base,cap(&x)?)?,cap(&a)?)?,cap(&b)?)?,96)?;
            for (total,value) in polynomial.iter_mut().zip(gkr::quadratic_message(&a,&b,&x)){*total+=value;}
        }Ok(polynomial)
    }
    fn high_input_value(d:&Descriptor<'_>,index:usize,chunk:usize,local:Fr,
        support:Option<&SupportControl>)->Fr{
        match support{
            Some(control) if control.fault==SupportFault::ZeroSkippedHighX&&!control.canonical(d,index,chunk)=>Fr::zero(),
            _=>local,
        }
    }
    fn phase(d:&Descriptor<'_>,kind:&Phase<'_>,index:usize,low:&Vec<Fr>,high:&Vec<Fr>,cache_bytes:usize,
        load:&mut impl FnMut(usize)->Result<Vec<Fr>,String>,audit:&mut Audit,
        claim:&mut Fr,rounds:&mut Vec<Vec<Fr>>,t:&mut Transcript,
        progress:&mut dyn FnMut(Native5Progress)->Result<(),String>,
        mut support:Option<&mut SupportControl>)->Result<(Vec<Fr>,Fr),String>{
        let width=audit.width;let chunks=d.input_len()/width;let mut point=Vec::with_capacity(d.input_log());
        let borrowed=match kind{Phase::Right{u,..}=>cap(u)?,_=>0};
        for _ in 0..d.chunk_bits(){
            let polynomial=low_message(d,kind,index,low,high,cache_bytes,load,audit,rounds,&point,support.as_deref_mut())?;
            point.push(accept_stream_round(polynomial,claim,rounds,t)?);
            if point.len()<d.input_log(){
                progress(Native5Progress::Round{side:if index==1{Native5Side::U}else{Native5Side::V},completed:point.len()})?;
            }
        }
        let mut a=Vec::with_capacity(chunks);let mut b=Vec::with_capacity(chunks);let mut x=Vec::with_capacity(chunks);
        let round_cap_before=round_cap(rounds)?;
        let base=add(add(add(add(add(add(cache_bytes,cap(low)?)?,cap(high)?)?,round_cap(rounds)?)?,cap(&point)?)?,borrowed)?,
            add(add(cap(&a)?,cap(&b)?)?,cap(&x)?)?)?;
        for chunk in 0..chunks{
            let mut local=audit.read(index,chunk,base,load)?;
            for coordinate in &point{gkr::fold(&mut local,*coordinate);}
            let (aa,bb)=vectors(d,chunk,width,&point,kind,low,high);
            audit.observe(index,add(add(add(base,cap(&local)?)?,cap(&aa)?)?,cap(&bb)?)?,0)?;
            a.push(aa[0]);b.push(bb[0]);x.push(high_input_value(d,index,chunk,local[0],support.as_deref()));
        }
        while x.len()>1{
            let live=add(base,round_cap(rounds)?.checked_sub(round_cap_before).ok_or("linear round inventory")?)?;
            audit.observe(index,live,96)?;
            let polynomial=gkr::quadratic_message(&a,&b,&x);let z=accept_stream_round(polynomial,claim,rounds,t)?;
            gkr::fold(&mut a,z);gkr::fold(&mut b,z);gkr::fold(&mut x,z);point.push(z);
            audit.stats.high_fold_coordinates[index-1]+=1;
            if point.len()<d.input_log(){
                progress(Native5Progress::Round{side:if index==1{Native5Side::U}else{Native5Side::V},completed:point.len()})?;
            }
        }
        audit.observe(index,add(base,round_cap(rounds)?.checked_sub(round_cap_before).ok_or("linear final round inventory")?)?,0)?;
        Ok((point,x[0]))
    }
    pub(crate) fn prove(d:&Descriptor<'_>,source_len:usize,retained_capacity_bytes:usize,
        load:impl FnMut(usize)->Result<Vec<Fr>,String>,t:&mut Transcript)
        ->Result<(GkrProof,InputClaim,Stats),String>{
        d.validate(source_len,d.chunk_bits())?;
        prove_inner(d,retained_capacity_bytes,load,t,None,&mut |_|Ok(()),None)
    }
    fn transaction<T>(t:&mut Transcript,run:impl FnOnce(&mut Transcript)->Result<T,String>)->Result<T,String>{
        let mut working=t.clone();let result=run(&mut working)?;*t=working;Ok(result)
    }
    pub(crate) fn prove_native_role5_for_test(
        admission:&crate::native_prefix_auth_plan::NativeRole5Admission<'_, '_>,
        t:&mut Transcript,additive_retained:usize)->Result<(GkrProof,InputClaim,Stats),String>{
        let d=admission.descriptor()?;d.validate_native(admission)?;
        let retained=add(admission.fixed_retained_capacity_bytes()?,additive_retained)?;
        // Refuse an excessive/overflowing complete charge before preparing the
        // fallible full-plan binder (which may allocate bounded JSON scratch).
        Audit::new(&d,retained)?;
        let prepared=admission.prepare_binding(t)?;
        transaction(t,|working|prove_inner(&d,retained,|chunk|admission.load_chunk(chunk),working,
            Some(prepared),&mut |event|admission.progress(event),None))
    }
    fn supported_run(d:&Descriptor<'_>,retained_with_control:usize,
        load:impl FnMut(usize)->Result<Vec<Fr>,String>,t:&mut Transcript,prepared:Option<Transcript>,
        progress:&mut dyn FnMut(Native5Progress)->Result<(),String>,mut control:SupportControl)
        ->Result<(GkrProof,InputClaim,Stats,SupportStats),String>{
        transaction(t,|working|{
            let (proof,claim,stats)=prove_inner(d,retained_with_control,load,working,prepared,progress,Some(&mut control))?;
            control.complete(d)?;
            Ok((proof,claim,stats,control.stats.clone()))
        })
    }
    /// A separate sealed entry; the complete-scan native entry above is retained.
    pub(crate) fn prove_native_role5_sparse_support_for_test(
        admission:&crate::native_prefix_auth_plan::NativeRole5Admission<'_, '_>,
        t:&mut Transcript,additive_retained:usize)->Result<(GkrProof,InputClaim,Stats,SupportStats),String>{
        let d=admission.descriptor()?;d.validate_native(admission)?;
        let control=SupportControl::new(&d,SupportFault::None)?;
        let retained=add(add(admission.fixed_retained_capacity_bytes()?,additive_retained)?,control.stats.control_capacity_bytes)?;
        Audit::new(&d,retained)?; // Includes the separate control reservation before binding/reads.
        let prepared=admission.prepare_binding(t)?;
        supported_run(&d,retained,|chunk|admission.load_chunk(chunk),t,Some(prepared),
            &mut |event|admission.progress(event),control)
    }
    /// The same arithmetic/support body, with a separate borrowed Historical
    /// capability. Generic and Native descriptor admissions stay unchanged.
    pub(crate) fn prove_historical50_role5_for_test(
        admission:&crate::historical_prefix_proof::Historical50Role5Admission<'_, '_>,t:&mut Transcript,
    )->Result<(GkrProof,InputClaim,Stats,SupportStats),String>{
        let d=admission.descriptor()?;d.validate_historical50(admission)?;
        let control=SupportControl::new(&d,SupportFault::None)?;
        let retained=add(admission.extra_live_capacity_bytes(),control.stats.control_capacity_bytes)?;
        Audit::new(&d,retained)?;
        let prepared=admission.prepare_binding(t)?;
        let result=supported_run(&d,retained,|chunk|admission.load_chunk(chunk),t,Some(prepared),
            &mut |event|admission.progress(event),control)?;
        admission.complete()?;Ok(result)
    }
    fn supported_n3(layout:&crate::header_adjacency_layout::HeaderAdjacencyLayout,source_len:usize,
        retained:usize,load:impl FnMut(usize)->Result<Vec<Fr>,String>,t:&mut Transcript,
        fault:SupportFault,progress:&mut dyn FnMut(Native5Progress)->Result<(),String>)
        ->Result<(GkrProof,InputClaim,Stats,SupportStats),String>{
        // Obtain the canonical small descriptor BEFORE any support/load/binding
        // activity; this factory refuses native32, even with an arbitrary callback.
        let d=layout.linear_descriptor_for_test()?;
        if d.active()!=3||d.padded()!=4{return Err("support seam requires canonical N3/four owners".into());}
        d.validate(source_len,d.chunk_bits())?;
        let control=SupportControl::new(&d,fault)?;
        let retained=add(retained,control.stats.control_capacity_bytes)?;
        Audit::new(&d,retained)?;
        supported_run(&d,retained,load,t,None,progress,control)
    }
    pub(crate) fn prove_sparse_support_n3_for_test(
        layout:&crate::header_adjacency_layout::HeaderAdjacencyLayout,source_len:usize,retained:usize,
        load:impl FnMut(usize)->Result<Vec<Fr>,String>,t:&mut Transcript)
        ->Result<(GkrProof,InputClaim,Stats,SupportStats),String>{
        supported_n3(layout,source_len,retained,load,t,SupportFault::None,&mut |_|Ok(()))
    }
    /// Separate arbitrary-witness H21 lane. Sparse support skips only low
    /// coefficient work. High phases read every original chunk; the line reads
    /// the same original bits as 16 contiguous chunks per physical owner.
    pub(crate) fn prove_h21_role5_candidate(d:&Descriptor<'_>,candidate:&crate::packed::UntrustedH21CandidateFile,
        budget:H21Role5Budget,prepared:&Transcript)->Result<(GkrProof,InputClaim,Stats,SupportStats),String>{
        d.validate_h21(candidate.untrusted_polynomial().input_len())?;
        let audit=Audit::h21(d,budget)?;
        if prepared.challenges()!=0||prepared.raw_queries()!=0{return Err("H21 role5 prepared prefix is not fresh".into());}
        let mut control=SupportControl::new(d,SupportFault::None)?;
        let mut t=prepared.clone();
        transaction(&mut t,|working| {
            let (proof,claim,stats)=prove_inner_audited(d,
                |chunk|candidate.untrusted_polynomial().read_copy(1<<16,chunk)
                    .map_err(|e|format!("H21 role5 held chunk: {e}")),
                working,Some(prepared.clone()),&mut |_|Ok(()),Some(&mut control),audit,Some(candidate))?;
            control.complete(d)?;Ok((proof,claim,stats,control.stats.clone()))
        })
    }
    /// Accounting-boundary controls only; no phase arrays or source are made.
    pub(crate) fn h21_role5_audit_controls_for_test(d:&Descriptor<'_>,budget:H21Role5Budget)->Result<Stats,String>{
        let mut audit=Audit::h21(d,budget)?;
        let room=audit.stats.preflight_bound_bytes.checked_sub(add(audit.stats.retained_capacity_bytes,FIXED_BOUND)?)
            .ok_or("H21 role5 audit room")?;
        audit.observe(1,room,0)?;
        if audit.observe(1,add(room,1)?,0).err().as_deref()!=Some("linear actual vector inventory exceeds preflight") {
            return Err("H21 role5 audit upper boundary".into());
        }
        Ok(audit.stats)
    }

    // Only the validated callback wrapper and computed-capability wrappers call
    // this arithmetic body. No caller-selected loader reaches native32.
    fn prove_inner(d:&Descriptor<'_>,retained_capacity_bytes:usize,
        load:impl FnMut(usize)->Result<Vec<Fr>,String>,t:&mut Transcript,
        prepared:Option<Transcript>,progress:&mut dyn FnMut(Native5Progress)->Result<(),String>,
        support:Option<&mut SupportControl>)
        ->Result<(GkrProof,InputClaim,Stats),String>{
        let audit=Audit::new(d,retained_capacity_bytes)?;
        prove_inner_audited(d,load,t,prepared,progress,support,audit,None)
    }

    pub(crate) fn original_chunk_line(x:&[Fr],chunk:usize,low:usize,u:&[Fr],v:&[Fr])
        ->(Vec<Fr>,Vec<Fr>,Vec<Fr>){
        let local=gkr::line_polynomial(x,&u[..low],&v[..low]);
        let selector=selector_line(chunk,&u[low..],&v[low..]);
        let contribution=multiply(&local,&selector);
        (local,selector,contribution)
    }

    fn prove_inner_audited(d:&Descriptor<'_>,mut load:impl FnMut(usize)->Result<Vec<Fr>,String>,t:&mut Transcript,
        prepared:Option<Transcript>,progress:&mut dyn FnMut(Native5Progress)->Result<(),String>,
        mut support:Option<&mut SupportControl>,mut audit:Audit,packed_line:Option<&crate::packed::UntrustedH21CandidateFile>)
        ->Result<(GkrProof,InputClaim,Stats),String>{
        let width=audit.width;let chunks=d.input_len()/width;let stride=d.ids().div_ceil(8);
        let mut parents=vec![0u8;d.active()*stride];let mut digests=vec![0u8;d.active()*stride];
        let started=Instant::now();
        for chunk in 0..chunks{
            let x=audit.read(0,chunk,add(cap(&parents)?,cap(&digests)?)?,&mut load)?;
            let first=chunk*width;let end=first+width;
            if first>>d.local_input()>=d.active(){audit.stats.initial_padding_chunks+=1;}
            for owner in first>>d.local_input()..=((end-1)>>d.local_input()).min(d.active()-1){
                for j in 0..d.ids(){for (wire,cache) in [(d.parent()[j],&mut parents),(d.digest()[j],&mut digests)]{
                    let at=(owner<<d.local_input())+wire;
                    if at>=first&&at<end&&x[at-first].is_one(){cache[owner*stride+j/8]|=1<<(j%8);}
                }}
            }
        }
        for j in 0..d.ids(){
            if cached(&parents,stride,0,j)!=d.start_bit(j)||cached(&digests,stride,d.active()-1,j)!=d.tip_bit(j)
                ||(1..d.active()).any(|i|cached(&digests,stride,i-1,j)!=cached(&parents,stride,i,j)){
                return Err("nonzero linear adjacency residual".into());
            }
        }
        drop(digests);audit.stats.phase_ns[0]=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"linear timer")?;
        progress(Native5Progress::ValidationComplete)?;
        let started=Instant::now();
        match prepared{Some(bound)=>*t=bound,None=>d.bind(t)}
        let r=gkr::output_point(d.row_count(),t);gkr::append_usize(t,b"gkr-layer-index",0);
        // eq_weights is unchanged; reserve its old/new construction overlap
        // separately from the actual returned vector capacities below.
        audit.observe(1,add(cap(&parents)?,cap(&r)?)?,
            add(mul(add(1usize<<d.local_row(),d.padded())?,128)?,1024)?)?;
        let low=gkr::eq_weights(&r[..d.local_row()]);let high=gkr::eq_weights(&r[d.local_row()..]);
        let mut claim=Fr::zero();let mut rounds=Vec::with_capacity(2*d.input_log());
        let (u,left_value)=phase(d,&Phase::Left(&parents),1,&low,&high,add(cap(&parents)?,cap(&r)?)?,
            &mut load,&mut audit,&mut claim,&mut rounds,t,progress,support.as_deref_mut())?;drop(parents);
        audit.stats.phase_ns[1]=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"linear timer")?;
        // Complete the final round mark after phase accounting so its interval
        // rigorously bounds phase_ns, including the final audit/return.
        progress(Native5Progress::Round{side:Native5Side::U,completed:d.input_log()})?;
        let mut endpoint=Fr::zero();for j in 0..d.ids(){
            endpoint+=low[j]*high[0]*eq_index(&u,d.parent()[j])*(left_value-d.start_bit(j));
            endpoint+=low[d.ids()+j]*high[d.active()-1]*eq_index(&u,((d.active()-1)<<d.local_input())+d.digest()[j])*(left_value-d.tip_bit(j));
        }
        let started=Instant::now();let (v,right_value)=phase(d,&Phase::Right{u:&u,value:left_value,endpoint},2,&low,&high,cap(&r)?,
            &mut load,&mut audit,&mut claim,&mut rounds,t,progress,support.as_deref_mut())?;
        audit.stats.phase_ns[2]=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"linear timer")?;
        progress(Native5Progress::Round{side:Native5Side::V,completed:d.input_log()})?;
        let coefficients=d.coefficients(&r,&u,&v)?;
        if coefficients[0]+coefficients[1]*left_value+coefficients[2]*right_value
            +coefficients[3]*left_value*right_value!=claim{return Err(GkrError::TerminalExpression.to_string());}
        drop(low);drop(high);drop(r);
        let started=Instant::now();
        let state=add(add(round_cap(&rounds)?,cap(&u)?)?,cap(&v)?)?;
        let (line,line_reads)=if let Some(source)=packed_line{
            use crate::sparse_stream_roster::h21_table_line;
            // chunk = (owner << 4) | bank: the four bank bits are now
            // local axes 16..20 and the remaining 21 axes still select owner.
            if d.chunk_bits()!=16 || d.local_input()!=20 || chunks!=16*h21_table_line::OWNERS{
                return Err("H21 adjacency packed line geometry".into());
            }
            audit.observe(3,state,h21_table_line::scratch_bytes()?)?;
            let line=h21_table_line::full(h21_table_line::Role::Adjacency,source,&u,&v)?;
            // Full checked exactly one packed physical read per owner. No
            // input field elements were reconstructed by the phase-3 loader.
            audit.stats.read_calls[3]=h21_table_line::OWNERS as u64;
            (line,h21_table_line::OWNERS)
        }else{
            let mut line=vec![Fr::zero();d.input_log()+1];
            let base=add(state,cap(&line)?)?;
            for chunk in 0..chunks{
                let x=audit.read(3,chunk,base,&mut load)?;
                let helper=add(mul(width,64)?,4096)?;
                audit.observe(3,add(base,cap(&x)?)?,helper)?;
                let (local,selector,contribution)=original_chunk_line(&x,chunk,d.chunk_bits(),&u,&v);
                audit.observe(3,add(add(add(add(base,cap(&x)?)?,cap(&local)?)?,cap(&selector)?)?,cap(&contribution)?)?,0)?;
                for (total,value) in line.iter_mut().zip(contribution){*total+=value;}
            }
            (line,chunks)
        };
        if line[0]!=left_value||gkr::eval_polynomial(&line,Fr::one())!=right_value{return Err(GkrError::LineEndpoints.to_string());}
        t.append_scalar(b"gkr-left-value",&left_value);t.append_scalar(b"gkr-right-value",&right_value);
        gkr::append_polynomial(t,b"gkr-line-polynomial",&line);let z=t.challenge_scalar(b"gkr-line-challenge");
        let point=gkr::line_point(&u,&v,z);let value=gkr::eval_polynomial(&line,z);
        audit.observe(3,add(add(add(add(round_cap(&rounds)?,cap(&u)?)?,cap(&v)?)?,cap(&line)?)?,cap(&point)?)?,0)?;
        audit.stats.phase_ns[3]=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"linear timer")?;
        audit.stats.line_input_fields=d.input_len();
        progress(Native5Progress::LineComplete)?;
        let expected=if let Some(control)=support.as_deref(){
            control.complete(d)?;
            [chunks,add(mul(d.chunk_bits(),control.stats.support_chunks[0])?,chunks)?,
                add(mul(d.chunk_bits(),control.stats.support_chunks[1])?,chunks)?,line_reads]
        }else{[chunks,(d.chunk_bits()+1)*chunks,(d.chunk_bits()+1)*chunks,line_reads]};
        if audit.stats.read_calls!=expected.map(|x|x as u64)
            ||audit.stats.high_fold_coordinates!=[d.input_log()-d.chunk_bits();2]{return Err("linear complete read/fold census".into());}
        let proof=GkrProof{layers:vec![LayerProof{rounds,left_value,right_value,line_coefficients:line}]};
        audit.observe(3,add(add(add(add(cap(&proof.layers)?,round_cap(&proof.layers[0].rounds)?)?,
            cap(&proof.layers[0].line_coefficients)?)?,cap(&point)?)?,add(cap(&u)?,cap(&v)?)?)?,0)?;
        progress(Native5Progress::ProducerComplete)?;
        Ok((proof,InputClaim{point,value},audit.stats))
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        fn fingerprint(t:&Transcript)->([u64;3],Fr){
            ([t.challenges(),t.raw_queries(),t.bytes_absorbed()],t.clone().challenge_scalar(b"linear-prepared-continuation"))
        }
        fn support_fixture()->(crate::header_adjacency_layout::HeaderAdjacencyLayout,Vec<Fr>){
            use crate::header_adjacency_layout::HeaderAdjacencyLayout;
            let layout=HeaderAdjacencyLayout::compile(3,2,[0x95;32],[0x63;32]).unwrap();
            let d=layout.linear_descriptor_for_test().unwrap();
            let mut input=(0..d.input_len()).map(|i|Fr::from(((i*13+i/19+7)%17<8) as u64)).collect::<Vec<_>>();
            let digest=|owner:usize,j:usize|if owner==2{d.tip_bit(j)}else{Fr::from(((owner*11+j*3+j/7)%5<2) as u64)};
            for owner in 0..3{for j in 0..256{
                input[(owner<<20)+d.parent()[j]]=if owner==0{d.start_bit(j)}else{digest(owner-1,j)};
                input[(owner<<20)+d.digest()[j]]=digest(owner,j);
            }}
            // Entire unsupported active and padding chunks remain nonzero. They
            // must contribute to high X and the line despite no low A/B support.
            for chunk in [9,11,27,43,49]{input[chunk*65536..(chunk+1)*65536].fill(Fr::one());}
            (layout,input)
        }
        fn message_differs_at_field_point(a:&[Fr],b:&[Fr])->bool{
            // A nonzero degree<=2 difference cannot vanish at all these distinct
            // nonboolean points. This isolates the message, not an earlier Err.
            (2u64..=5).any(|n|gkr::eval_polynomial(a,Fr::from(n))!=gkr::eval_polynomial(b,Fr::from(n)))
        }
        #[test]
        fn sparse_support_n3_messages_consumers_and_reached_faults(){
            use crate::header_adjacency_layout::HeaderAdjacencyLayout;
            use std::cell::Cell;
            assert_eq!(std::mem::size_of::<SupportStats>(),72);
            assert_eq!(std::mem::size_of::<SupportControl>(),80);
            assert_eq!(SupportControl::capacity_bound().unwrap(),256);
            let (layout,input)=support_fixture();let d=layout.linear_descriptor_for_test().unwrap();
            let width=1usize<<d.chunk_bits();let retained=cap(&input).unwrap();
            let start=||{let mut t=Transcript::new(b"role5-support-n3-differential");t.append_bytes(b"existing-prefix",b"keep");t};
            let mut full_t=start();let (full,full_claim,full_stats)=prove(&d,input.len(),retained,
                |chunk|Ok(input[chunk*width..(chunk+1)*width].to_vec()),&mut full_t).unwrap();
            let mut selected_t=start();let (selected,claim,stats,support)=prove_sparse_support_n3_for_test(&layout,input.len(),retained,
                |chunk|Ok(input[chunk*width..(chunk+1)*width].to_vec()),&mut selected_t).unwrap();
            assert_eq!(selected,full);assert_eq!(claim,full_claim);assert_eq!(fingerprint(&selected_t),fingerprint(&full_t));
            let packet=gkr::encode_proof(&selected).unwrap();
            assert_eq!(packet,gkr::encode_proof(&full).unwrap());assert_eq!(packet.len(),32*(7*22+3));
            assert_eq!(full_stats.read_calls,[64,1088,1088,64]);assert_eq!(stats.read_calls,[64,128,112,64]);
            assert_eq!(stats.reconstructed_fields,stats.read_calls.map(|x|x*65536));
            assert_eq!(stats.high_fold_coordinates,[6,6]);assert_eq!(stats.initial_padding_chunks,16);
            assert_eq!(support.support_chunks,[4,3]);assert_eq!(support.low_round_read_calls,[64,48]);
            assert_eq!(support.low_round_skipped_chunks,[960,976]);assert_eq!(support.control_capacity_bytes,256);
            assert_eq!(stats.retained_capacity_bytes,retained+256);
            assert_eq!(stats.preflight_bound_bytes,full_stats.preflight_bound_bytes+256);
            let mut verifier=start();let verified=gkr::verify_with_wiring(&[22],1usize<<11,&selected,&mut verifier,
                |t|layout.bind(t),|layer,r,u,v|{
                    assert_eq!(layer,0);layout.coefficients(r,u,v).map_err(|_|GkrError::PointDimension)
                }).unwrap();
            assert_eq!(verified,claim);assert_eq!(fingerprint(&verifier),fingerprint(&selected_t));
            assert_eq!(gkr::mle(&input,&claim.point).unwrap(),claim.value);

            // A canonical descriptor cannot grant arbitrary-callback native32
            // support. Refusal precedes any load, binding or transcript change.
            let native=HeaderAdjacencyLayout::compile(3073,12,[0;32],[0;32]).unwrap();
            let calls=Cell::new(0);let mut t=start();let before=fingerprint(&t);
            let rejected=prove_sparse_support_n3_for_test(&native,1usize<<32,0,
                |_|{calls.set(calls.get()+1);panic!("native callback must not load")},&mut t);
            assert_eq!(rejected.unwrap_err(),"linear diagnostic requires canonical N3/N4 layout");
            assert_eq!(calls.get(),0);assert_eq!(fingerprint(&t),before);
            let mut t=start();let before=fingerprint(&t);
            assert_eq!(prove_sparse_support_n3_for_test(&layout,input.len(),usize::MAX,
                |_|panic!("control charge overflow before read"),&mut t).unwrap_err(),"linear capacity sum overflow");
            assert_eq!(fingerprint(&t),before);

            // Exhaustive chunk membership is structural, independent of prefix.
            // All omitted chunks have both A AND B zero at nonboolean prefixes.
            let mut parents=vec![0u8;3*32];
            for owner in 0..3{for j in 0..256{if input[(owner<<20)+d.parent()[j]].is_one(){parents[owner*32+j/8]|=1<<(j%8);}}}
            let low=gkr::eq_weights(&vec![Fr::from(2u64);9]);
            let high=gkr::eq_weights(&vec![Fr::from(3u64);2]);
            let u=vec![Fr::from(5u64);22];let left=Fr::from(11u64);let endpoint=Fr::from(7u64);
            let kinds=[Phase::Left(&parents),Phase::Right{u:&u,value:left,endpoint}];
            let control=SupportControl::new(&d,SupportFault::None).unwrap();
            for (side,kind) in kinds.iter().enumerate(){let phase=side+1;
                assert_eq!((0..64).filter(|chunk|control.contains(&d,phase,*chunk)).count(),[4,3][side]);
                for prefix in [vec![],vec![Fr::from(2u64),Fr::from(3u64),Fr::from(5u64)]]{
                    for chunk in 0..64{if !control.contains(&d,phase,chunk){
                        let (a,b)=vectors(&d,chunk,width,&prefix,kind,&low,&high);
                        assert!(a.iter().all(Zero::is_zero)&&b.iter().all(Zero::is_zero),"omitted A/B phase{phase} chunk{chunk}");
                    }}
                }
            }
            // Select bit4 explicitly: genesis bits4/5 are1/0 and tip bits4/5
            // are0/1. Their low messages are therefore nonzero multiples of
            // z*(1-z), guaranteeing these isolated omissions are observable.
            let mut low=vec![Fr::zero();512];low[4]=Fr::one();low[260]=Fr::one();
            let prefix=Vec::new();let rounds=Vec::new();
            let (a,b)=vectors(&d,0,width,&prefix,&kinds[1],&low,&high);
            assert!(a.iter().all(Zero::is_zero));assert!(b.iter().any(|x|!x.is_zero()));
            for (fault,phase,target,wrong) in [
                (SupportFault::OmitGenesis,1,8,None),(SupportFault::OmitTip,1,42,None),
                (SupportFault::OmitGlobalZero,2,0,None),(SupportFault::AOnly,2,0,None),
                (SupportFault::WrongChunk,1,8,Some(9)),
            ]{
                let mut mutant=SupportControl::new(&d,fault).unwrap();
                assert!(control.contains(&d,phase,target));assert!(!mutant.contains(&d,phase,target));
                if let Some(wrong)=wrong{assert!(!control.contains(&d,phase,wrong));assert!(mutant.contains(&d,phase,wrong));}
                let (a,b)=vectors(&d,target,width,&prefix,&kinds[phase-1],&low,&high);
                assert!(a.iter().chain(&b).any(|v|!v.is_zero()),"affected coefficients {fault:?}");
                let mut original_audit=Audit::new(&d,retained+256).unwrap();
                let mut changed_audit=Audit::new(&d,retained+256).unwrap();let mut hit=false;
                let original=low_message(&d,&kinds[phase-1],phase,&low,&high,cap(&parents).unwrap(),
                    &mut |chunk|Ok(input[chunk*width..(chunk+1)*width].to_vec()),&mut original_audit,&rounds,&prefix,None).unwrap();
                let changed=low_message(&d,&kinds[phase-1],phase,&low,&high,cap(&parents).unwrap(),
                    &mut |chunk|{if Some(chunk)==wrong{hit=true;}Ok(input[chunk*width..(chunk+1)*width].to_vec())},
                    &mut changed_audit,&rounds,&prefix,Some(&mut mutant)).unwrap();
                if wrong.is_some(){assert!(hit,"wrong chunk actually read");}
                assert!(message_differs_at_field_point(&original,&changed),"actual low helper differential {fault:?}");
            }

            // Same high-handoff selector as production, with independent prefix
            // reconstruction. Zeroing unsupported X preserves A/B but changes
            // the real first high-round message once neighboring buckets mix.
            let prefix=vec![Fr::from(2u64);16];let fault=SupportControl::new(&d,SupportFault::ZeroSkippedHighX).unwrap();
            let mut aa=Vec::new();let mut bb=Vec::new();let mut xx=Vec::new();let mut bad=Vec::new();
            for chunk in 0..64{
                let mut local=input[chunk*width..(chunk+1)*width].to_vec();
                for z in &prefix{gkr::fold(&mut local,*z);}
                let (a,b)=vectors(&d,chunk,width,&prefix,&kinds[0],&low,&high);
                aa.push(a[0]);bb.push(b[0]);
                xx.push(high_input_value(&d,1,chunk,local[0],Some(&control)));
                bad.push(high_input_value(&d,1,chunk,local[0],Some(&fault)));
            }
            assert_eq!(xx[9],Fr::one());assert_eq!(bad[9],Fr::zero());
            assert!(message_differs_at_field_point(&gkr::quadratic_message(&aa,&bb,&xx),
                &gkr::quadratic_message(&aa,&bb,&bad)),"actual high helper differential");

            // Loader faults are reached exactly, including skipped chunk1 in
            // full U handoff and line. Stage follows actual accepted progress.
            for (at,mode,expected_stage,expected_error) in [
                (1,0,0,"isolated support read"),(1,1,0,"linear short/oversized chunk"),
                (1,2,0,"linear short/oversized chunk"),(2,3,0,"linear non-Boolean chunk"),
                (130,0,16,"isolated support read"),(306,0,44,"isolated support read"),
            ]{
                let calls=Cell::new(0usize);let stage=Cell::new(0usize);let hit=Cell::new(false);let mut t=start();let before=fingerprint(&t);
                let result=supported_n3(&layout,input.len(),retained,|chunk|{
                    let call=calls.get()+1;calls.set(call);
                    if call==at{
                        hit.set(true);assert_eq!(stage.get(),expected_stage);
                        if at>64{assert_eq!(chunk,1,"late unsupported chunk reached");}
                        if mode==0{return Err("isolated support read".into());}
                        if mode==1{return Ok(vec![Fr::zero();width-1]);}
                        if mode==2{let mut x=Vec::with_capacity(width+1);x.resize(width,Fr::zero());return Ok(x);}
                        assert_eq!(chunk,1);let mut x=input[chunk*width..(chunk+1)*width].to_vec();x[0]=Fr::from(2u64);return Ok(x);
                    }Ok(input[chunk*width..(chunk+1)*width].to_vec())
                },&mut t,SupportFault::None,&mut |event|{
                    match event{Native5Progress::ValidationComplete=>stage.set(0),
                        Native5Progress::Round{side:Native5Side::U,completed}=>stage.set(completed),
                        Native5Progress::Round{side:Native5Side::V,completed}=>stage.set(22+completed),_=>()}
                    Ok(())
                });
                assert!(hit.get());assert_eq!(calls.get(),at);assert_eq!(result.unwrap_err(),expected_error);
                assert_eq!(fingerprint(&t),before);
            }
            let mut t=start();let before=fingerprint(&t);let mut hit=false;
            let result=supported_n3(&layout,input.len(),retained,
                |chunk|Ok(input[chunk*width..(chunk+1)*width].to_vec()),&mut t,SupportFault::None,&mut |event|{
                    if event==Native5Progress::ProducerComplete{hit=true;Err("isolated support progress".into())}else{Ok(())}
                });
            assert!(hit);assert_eq!(result.unwrap_err(),"isolated support progress");assert_eq!(fingerprint(&t),before);
        }
        #[test]
        fn prepared_binding_progress_and_transaction_preserve_default_proof(){
            let d=Descriptor::owner_toy();let mut input=vec![Fr::zero();d.input_len()];
            let width=1usize<<d.chunk_bits();
            input[8190]=Fr::one();input[8191]=Fr::one();
            let mut initial=Transcript::new(b"linear-prepared-control");
            initial.append_bytes(b"existing-prefix",b"preserved");
            let mut direct=initial.clone();
            let (expected,claim,stats)=prove(&d,input.len(),0,|chunk|Ok(input[chunk*width..(chunk+1)*width].to_vec()),&mut direct).unwrap();
            let mut prepared=initial.clone();d.bind(&mut prepared);
            let mut actual=initial.clone();let mut events=Vec::new();
            let (proof,got,measured)=transaction(&mut actual,|working|prove_inner(&d,0,
                |chunk|Ok(input[chunk*width..(chunk+1)*width].to_vec()),working,Some(prepared.clone()),&mut |event|{events.push(event);Ok(())},None)).unwrap();
            assert_eq!(proof,expected);assert_eq!(got,claim);assert_eq!(fingerprint(&actual),fingerprint(&direct));
            assert_eq!(measured.read_calls,stats.read_calls);assert_eq!(measured.high_fold_coordinates,[12,12]);
            assert_eq!(crate::gkr::encode_proof(&proof).unwrap(),crate::gkr::encode_proof(&expected).unwrap());
            let mut wanted=vec![Native5Progress::ValidationComplete];
            for side in [Native5Side::U,Native5Side::V]{for completed in 1..=13{
                wanted.push(Native5Progress::Round{side,completed});}}
            wanted.extend([Native5Progress::LineComplete,Native5Progress::ProducerComplete]);assert_eq!(events,wanted);
            for fault in [Native5Progress::ValidationComplete,
                Native5Progress::Round{side:Native5Side::U,completed:1},Native5Progress::ProducerComplete]{
                let mut t=initial.clone();let before=fingerprint(&t);let mut hit=false;
                let result=transaction(&mut t,|working|prove_inner(&d,0,|chunk|Ok(input[chunk*width..(chunk+1)*width].to_vec()),
                    working,Some(prepared.clone()),&mut |event|if event==fault{hit=true;Err("isolated progress failure".into())}else{Ok(())},None));
                assert!(hit);assert_eq!(result.unwrap_err(),"isolated progress failure");assert_eq!(fingerprint(&t),before);
            }
            assert!(preflight_for_test(&d,usize::MAX).is_err());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn maps() -> ([usize;256],[usize;256]) {
        (std::array::from_fn(|j|32+(j*73)%256), std::array::from_fn(|j|512+(j*151)%256))
    }
    fn relation(n:usize) -> Relation {
        let(p,d)=maps(); Relation::new(n,p,d,[0x95;32],[0x63;32]).unwrap()
    }
    fn point(bits:usize,seed:u64) -> Vec<Fr> {
        (0..bits).map(|j|Fr::from(seed+((j*j+3*j+7)%43) as u64)).collect()
    }
    fn boolean_point(bits:usize,index:usize)->Vec<Fr> {
        (0..bits).map(|j|Fr::from(((index>>j)&1) as u64)).collect()
    }
    // Independent oracle: construct all rows, including padded zero rows, then
    // evaluate every actual gate at direct Boolean basis polynomials.
    fn dense_coefficients(relation:&Relation,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
        let mut rows=vec![Vec::<Gate>::new();relation.row_count()];let z=Fr::zero();let o=Fr::one();
        for j in 0..256 {
            rows[j].push(Gate{left:relation.parent_wires[j],right:0,
                c0:-Fr::from(((relation.parent[j/8]>>(j%8))&1) as u64),c1:o,c2:z,c3:z});
            rows[(relation.n-1)*512+256+j].push(Gate{
                left:(relation.n-1)*(1<<relation.header_bits)+relation.digest_wires[j],right:0,
                c0:-Fr::from(((relation.tip[j/8]>>(j%8))&1) as u64),c1:o,c2:z,c3:z});
            for i in 1..relation.n {rows[i*512+j].push(Gate{
                left:(i-1)*(1<<relation.header_bits)+relation.digest_wires[j],
                right:i*(1<<relation.header_bits)+relation.parent_wires[j],c0:z,c1:o,c2:-o,c3:z});}
        }
        let basis=|p:&[Fr],index:usize| {
            let mut out=Fr::one();let mut digits=index;
            for x in p {out *= if digits%2==0 {Fr::one()-x}else{*x};digits/=2;} out
        };
        let mut out=[z;4];
        for(row,gates)in rows.iter().enumerate(){for g in gates{
            let w=basis(r,row)*basis(u,g.left)*basis(v,g.right);
            for (a,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]) {*a+=w*c;}
        }} out
    }
    fn input(relation:&Relation)->Vec<Fr> {
        let mut values=(0..relation.input_len()).map(|i|Fr::from((i%19) as u64)).collect::<Vec<_>>();
        for i in 0..relation.n {for j in 0..256 {
            let parent=if i==0 {id_bit(&relation.parent,j)}else{Fr::from(((i-1+j)%2) as u64)};
            let digest=if i==relation.n-1 {id_bit(&relation.tip,j)}else{Fr::from(((i+j)%2) as u64)};
            values[(i<<relation.header_bits)+relation.parent_wires[j]]=parent;
            values[(i<<relation.header_bits)+relation.digest_wires[j]]=digest;
        }} values
    }
    fn nonzero(rows:&[Fr])->Vec<usize>{rows.iter().enumerate().filter_map(|(i,v)|(!v.is_zero()).then_some(i)).collect()}

    #[test]
    fn fast_coefficients_match_independent_dense_rows_at_all_dimensions() {
        for n in [1,2,4] {let relation=relation(n);let rb=ROW_BITS+n.trailing_zeros() as usize;
            for seed in [2,17,101] {
                let r=point(rb,seed);let u=point(relation.input_log(),seed+33);let v=point(relation.input_log(),seed+77);
                assert_eq!(relation.coefficients(&r,&u,&v).unwrap(),dense_coefficients(&relation,&r,&u,&v));
            }
            // Byte/half/end boundaries and every active header link. The
            // arbitrary-field differential above includes all 256 bit terms.
            for j in [0,1,127,128,255] {
                for (row,left,right) in [(j,relation.parent_wires[j],0),
                    ((n-1)*512+256+j,((n-1)<<HEADER_BITS)+relation.digest_wires[j],0)] {
                    let r=boolean_point(rb,row);let u=boolean_point(relation.input_log(),left);let v=boolean_point(relation.input_log(),right);
                    assert_eq!(relation.coefficients(&r,&u,&v).unwrap(),dense_coefficients(&relation,&r,&u,&v));
                }
                for i in 1..n {let r=boolean_point(rb,i*512+j);
                    let u=boolean_point(relation.input_log(),((i-1)<<HEADER_BITS)+relation.digest_wires[j]);
                    let v=boolean_point(relation.input_log(),(i<<HEADER_BITS)+relation.parent_wires[j]);
                    assert_eq!(relation.coefficients(&r,&u,&v).unwrap(),[Fr::zero(),Fr::one(),-Fr::one(),Fr::zero()]);
                }
            }
        }
    }
    #[test]
    fn endpoints_use_global_zero_and_links_do_not_wrap() {
        for n in [1,2,4] {let rel=relation(n);let rb=ROW_BITS+n.trailing_zeros() as usize;
            let r=boolean_point(rb,0);let u=boolean_point(rel.input_log(),((n-1)<<HEADER_BITS)+rel.digest_wires[0]);
            let v=boolean_point(rel.input_log(),rel.parent_wires[0]);
            assert_eq!(rel.coefficients(&r,&u,&v).unwrap(),[Fr::zero();4]);
            if n>1 {
                let r=boolean_point(rb,(n-1)*512+256);let u=boolean_point(rel.input_log(),((n-1)<<HEADER_BITS)+rel.digest_wires[0]);
                let wrong_right=boolean_point(rel.input_log(),1<<HEADER_BITS);
                assert_eq!(rel.coefficients(&r,&u,&wrong_right).unwrap(),[Fr::zero();4]);
                let good=rel.coefficients(&r,&u,&vec![Fr::zero();rel.input_log()]).unwrap();assert_eq!(good[1],Fr::one());
            }
        }
    }
    #[test]
    fn residuals_isolate_first_last_and_each_interior_link() {
        for n in [1,2,4] {
            let mut rel=relation(n);rel.header_bits=10; // Small arithmetic differential, public constructor stays fixed20.
            let mut w=input(&rel);assert!(nonzero(&rel.residuals(&w).unwrap()).is_empty());
            for j in [0,127,255] {
                let index=rel.parent_wires[j];w[index]+=Fr::one();assert_eq!(nonzero(&rel.residuals(&w).unwrap()),vec![j]);w[index]-=Fr::one();
                let index=((n-1)<<10)+rel.digest_wires[j];w[index]+=Fr::one();
                assert_eq!(nonzero(&rel.residuals(&w).unwrap()),vec![(n-1)*512+256+j]);w[index]-=Fr::one();
                for i in 1..n {let index=(i<<10)+rel.parent_wires[j];w[index]+=Fr::one();
                    assert_eq!(nonzero(&rel.residuals(&w).unwrap()),vec![i*512+j]);
                    assert_eq!(rel.prove(&w,&mut Transcript::new(b"bad-adjacency")).err().unwrap(),"nonzero adjacency residual");w[index]-=Fr::one();}
            }
            let mut wrong=rel.clone();wrong.parent[0]^=1;assert_eq!(nonzero(&wrong.residuals(&w).unwrap()),vec![0]);
            let mut wrong=rel.clone();wrong.tip[31]^=128;assert_eq!(nonzero(&wrong.residuals(&w).unwrap()),vec![(n-1)*512+511]);
        }
    }
    #[test]
    fn chunk_line_equals_full_table_and_independent_off_endpoint_mle() {
        for bits in [0,1,4,9] {
            let input=(0..1usize<<bits).map(|i|Fr::from((i*i+3*i+11) as u64)).collect::<Vec<_>>();
            let u=point(bits,3);let v=point(bits,37);
            let full=gkr::line_polynomial(&input,&u,&v);
            for chunk in [0,1,3,16] {
                let line=chunked_line(&input,&u,&v,chunk).unwrap();assert_eq!(line,full);
                for t in [Fr::zero(),Fr::one(),Fr::from(2u64),Fr::from(13u64),-Fr::one()] {
                    let p=gkr::line_point(&u,&v,t);
                    let expected=input.iter().enumerate().fold(Fr::zero(),|sum,(i,x)|sum+*x*eq_index(&p,i));
                    assert_eq!(gkr::eval_polynomial(&line,t),expected);
                }
            }
        }
        // A quadratic index pattern cannot exercise the high coefficients.
        // This Boolean basis vector has a full-degree nine-variable MLE.
        let mut one_hot=vec![Fr::zero();512];one_hot[341]=Fr::one();
        let u=point(9,3);let v=point(9,37);
        let line=chunked_line(&one_hot,&u,&v,3).unwrap();
        assert_eq!(line.len(),10);assert!(!line[9].is_zero());
        assert_eq!(line,gkr::line_polynomial(&one_hot,&u,&v));
        for t in [Fr::from(2u64),Fr::from(13u64),-Fr::one()] {
            let p=gkr::line_point(&u,&v,t);
            assert_eq!(gkr::eval_polynomial(&line,t),eq_index(&p,341));
        }
        let constant=chunked_line(&one_hot,&u,&u,3).unwrap();
        assert_eq!(constant.len(),10);assert_eq!(constant[0],eq_index(&u,341));
        assert!(constant[1..].iter().all(Zero::is_zero));
        assert_eq!(constant,gkr::line_polynomial(&one_hot,&u,&u));
        assert!(chunked_line(&[Fr::one()],&[],&[],17).is_err());
        assert!(chunked_line(&[Fr::one()],&[Fr::one()],&[],1).is_err());
    }
    #[test]
    fn proof_uses_compact_binding_fast_verifier_and_strict_decoder() {
        for n in [1,2,4] {
            let mut rel=relation(n);assert_eq!(rel.input_log(),20+n.trailing_zeros() as usize);rel.header_bits=10;
            let w=input(&rel);let mut pt=Transcript::new(b"adjacency-test");
            let (proof,claim)=rel.prove(&w,&mut pt).unwrap();let bytes=gkr::encode_proof(&proof).unwrap();
            assert_eq!(bytes.len(),32*(7*rel.input_log()+3));
            let decoded=rel.decode_proof(&bytes).unwrap();let mut vt=Transcript::new(b"adjacency-test");
            assert_eq!(rel.verify(&decoded,&mut vt).unwrap(),claim);
            let expected=w.iter().enumerate().fold(Fr::zero(),|sum,(i,x)|sum+*x*eq_index(&claim.point,i));
            assert_eq!(claim.value,expected);assert_eq!(pt.bytes_absorbed(),vt.bytes_absorbed());
            assert_eq!(pt.raw_queries(),vt.raw_queries());assert_eq!(pt.challenge_scalar(b"next"),vt.challenge_scalar(b"next"));
            let mut trailing=bytes.clone();trailing.push(0);assert!(rel.decode_proof(&trailing).is_err());
            assert!(rel.decode_proof(&bytes[..bytes.len()-1]).is_err());
            let mut noncanonical=bytes.clone();noncanonical[..32].fill(0xff);assert!(rel.decode_proof(&noncanonical).is_err());
            let mut bad=proof.clone();bad.layers[0].rounds.pop();assert_eq!(rel.verify(&bad,&mut Transcript::new(b"adjacency-test")).err().unwrap(),GkrError::SumcheckRoundCount.to_string());
            let mut bad=proof.clone();bad.layers[0].line_coefficients.push(Fr::zero());
            assert_eq!(rel.verify(&bad,&mut Transcript::new(b"adjacency-test")).err().unwrap(),GkrError::LineDegree.to_string());
            let mut wrong=rel.clone();wrong.tip[0]^=1;assert!(wrong.verify(&proof,&mut Transcript::new(b"adjacency-test")).is_err());
        }
    }
    #[test]
    fn admission_and_descriptor_are_fixed_and_bounded() {
        let(p,d)=maps();for n in [0,3,5,8,usize::MAX] {assert!(Relation::new(n,p,d,[0;32],[0;32]).is_err());}
        let mut bad=p;bad[0]=1<<20;assert!(Relation::new(1,bad,d,[0;32],[0;32]).is_err());
        let mut bad=d;bad[0]=p[0];assert!(Relation::new(1,p,bad,[0;32],[0;32]).is_err());
        let mut bad=p;bad[0]=bad[1];assert!(Relation::new(1,bad,d,[0;32],[0;32]).is_err());
        let mut sizes=Vec::new();for n in [1,2,4] {let rel=relation(n);let mut t=Transcript::new(b"descriptor");rel.bind(&mut t);sizes.push(t.bytes_absorbed());
            assert!(rel.residuals(&[]).is_err());assert_eq!(rel.coefficients(&[],&[],&[]).unwrap_err(),GkrError::PointDimension);}
        assert!(sizes.iter().all(|x|*x==sizes[0]));
    }

    fn boolean_input(rel:&Relation)->Vec<Fr> {
        let mut values:Vec<_>=input(rel).iter().map(|x|Fr::from((!x.is_zero()) as u64)).collect();
        // The last wire lies outside both maps and still affects the global MLE.
        *values.last_mut().unwrap()=Fr::one();values
    }
    fn transcript_snapshot(t:&Transcript)->(u64,u64,u64,Fr) {
        let mut next=t.clone();(t.bytes_absorbed(),t.raw_queries(),t.challenges(),next.challenge_scalar(b"snapshot-next"))
    }

    #[test]
    fn streamed_boolean_proof_bytes_claim_and_transcript_equal_dense() {
        for n in [1,2,4] {
            let mut rel=relation(n);rel.header_bits=10;let w=boolean_input(&rel);
            let mut dense_t=Transcript::new(b"stream-parity");let dense=rel.prove(&w,&mut dense_t).unwrap();
            for b in [0usize,3,rel.input_log()] {
                let width=1usize<<b;let chunks=w.len()/width;let mut calls=0;
                let mut t=Transcript::new(b"stream-parity");
                let (proof,claim,stats)=rel.prove_streamed_reader(b,|chunk| {
                    calls+=1;Ok(w[chunk*width..(chunk+1)*width].to_vec())
                },&mut t).unwrap();
                assert_eq!(proof,dense.0);assert_eq!(claim,dense.1);
                assert_eq!(gkr::encode_proof(&proof).unwrap(),gkr::encode_proof(&dense.0).unwrap());
                assert_eq!(transcript_snapshot(&t),transcript_snapshot(&dense_t));
                assert_eq!(stats.chunk_reads,((2*b+4)*chunks) as u64);assert_eq!(stats.chunk_reads,calls);
                assert_eq!(stats.chunk_fields_max,width);assert_eq!(stats.transition_fields_max,3*chunks);
                let mut vt=Transcript::new(b"stream-parity");assert_eq!(rel.verify(&proof,&mut vt).unwrap(),claim);
                assert_eq!(transcript_snapshot(&t),transcript_snapshot(&vt));
            }
        }
    }

    #[test]
    fn streamed_prefix_vectors_equal_dense_with_zero_weights_and_cancellation() {
        for n in [1,2,4] {
            let mut rel=relation(n);rel.header_bits=10;let w=boolean_input(&rel);
            let mut parents=vec![[0u8;32];n];
            for header in 0..n {for j in 0..256 {if w[(header<<10)+rel.parent_wires[j]].is_one(){parents[header][j/8]|=1<<(j%8);}}}
            for seed in [0u64,1,7] {
                let rb=ROW_BITS+n.trailing_zeros() as usize;
                let r=if seed<2 {vec![Fr::from(seed);rb]}else{point(rb,seed)};
                let u=if seed<2 {vec![Fr::from(seed);rel.input_log()]}else{point(rel.input_log(),seed+3)};
                let low=gkr::eq_weights(&r[..ROW_BITS]);let high=gkr::eq_weights(&r[ROW_BITS..]);let rw=gkr::eq_weights(&r);
                let value=Fr::from(13u64);let mut endpoint=Fr::zero();
                rel.for_each_gate(|row,g| {if g.c2.is_zero(){endpoint+=rw[row]*eq_index(&u,g.left)*(g.c0+g.c1*value);}});
                let phases=[StreamPhase::Left {parents:&parents},StreamPhase::Right {u:&u,a:value,endpoint}];
                for phase in &phases {
                    let mut aa=vec![Fr::zero();w.len()];let mut bb=aa.clone();
                    rel.for_each_gate(|row,g| {match phase {
                        StreamPhase::Left {..}=>{aa[g.left]+=rw[row]*(g.c1+g.c3*w[g.right]);bb[g.left]+=rw[row]*(g.c0+g.c2*w[g.right]);},
                        StreamPhase::Right {..}=>{let weight=rw[row]*eq_index(&u,g.left);aa[g.right]+=weight*(g.c2+g.c3*value);bb[g.right]+=weight*(g.c0+g.c1*value);},
                    }});
                    let mut prefix=Vec::new();
                    for k in 0..=3 {
                        let mut actual_a=Vec::new();let mut actual_b=Vec::new();
                        for chunk in 0..w.len()/8 {let(a,b)=rel.stream_vectors(chunk,8,&prefix,phase,&low,&high);actual_a.extend(a);actual_b.extend(b);}
                        assert_eq!(actual_a,aa);assert_eq!(actual_b,bb);
                        if k<3 {let z=[Fr::zero(),Fr::one(),Fr::from(7u64)][k];prefix.push(z);gkr::fold(&mut aa,z);gkr::fold(&mut bb,z);}
                    }
                }
            }
        }
        // Nonzero contributions collide and cancel after binding the low bit.
        let p=std::array::from_fn(|j|32+j);let d=std::array::from_fn(|j|512+j);
        let mut rel=Relation::new(1,p,d,[0x01;32],[0;32]).unwrap();rel.header_bits=10;
        let mut low=vec![Fr::zero();512];low[0]=Fr::one();low[1]=-Fr::one();
        let half=Fr::one()/Fr::from(2u64);let parents=[[0x01;32]];
        let (a,b)=rel.stream_vectors(4,8,&[half],&StreamPhase::Left {parents:&parents},&low,&[Fr::one()]);
        assert!(a.iter().all(Zero::is_zero));assert_eq!(b[0],-half);
        assert!(b.iter().skip(1).all(Zero::is_zero));
    }

    #[test]
    fn streamed_line_retains_off_support_full_degree_and_equal_endpoints() {
        let mut rel=relation(1);rel.header_bits=10;let mut w=vec![Fr::zero();rel.input_len()];
        let last=w.len()-1;w[last]=Fr::one();assert!(!rel.parent_wires.contains(&last)&&!rel.digest_wires.contains(&last));
        let u=point(rel.input_log(),3);let v=point(rel.input_log(),37);
        let mut stats=StreamStats::default();
        let line=rel.stream_line(3,&u,&v,&mut |chunk|Ok(w[chunk*8..(chunk+1)*8].to_vec()),&mut stats).unwrap();
        assert_eq!(line,gkr::line_polynomial(&w,&u,&v));assert_eq!(line.len(),rel.input_log()+1);
        assert!(!line[rel.input_log()].is_zero());assert_eq!(stats.chunk_reads,(w.len()/8) as u64);
        for t in [Fr::from(2u64),Fr::from(13u64),-Fr::one()] {
            assert_eq!(gkr::eval_polynomial(&line,t),eq_index(&gkr::line_point(&u,&v,t),last));
        }
        let constant=rel.stream_line(3,&u,&u,&mut |chunk|Ok(w[chunk*8..(chunk+1)*8].to_vec()),&mut StreamStats::default()).unwrap();
        assert_eq!(constant.len(),line.len());assert!(constant[1..].iter().all(Zero::is_zero));
        assert_eq!(constant[0],eq_index(&u,last));
        let local=gkr::line_polynomial(&w[w.len()-8..],&u[..3],&v[..3]);
        let wrong=multiply(&local,&selector_line(w.len()/8-1,&v[3..],&u[3..]));
        assert_ne!(line,wrong); // Mutated expression differs from the reference.
        let mut trimmed=line.clone();trimmed.pop();assert_ne!(trimmed,line);
    }

    #[test]
    fn streamed_reader_faults_are_fail_closed_on_initial_and_later_reads() {
        let mut rel=relation(1);rel.header_bits=10;let w=boolean_input(&rel);let chunks=w.len()/8;
        for failing_call in [1,chunks+1,5*chunks+1,9*chunks+1] {for fault in 0..4 {
            let mut t=Transcript::new(b"stream-read-error");let before=transcript_snapshot(&t);let mut calls=0;
            let result=rel.prove_streamed_reader(3,|chunk| {
                calls+=1;if calls==failing_call && fault==0 {return Err("injected read failure".into());}
                let mut x=w[chunk*8..(chunk+1)*8].to_vec();
                if calls==failing_call {match fault {1=>{x.pop();},2=>x.push(Fr::zero()),3=>x[0]=Fr::from(2u64),_=>{}}}
                Ok(x)
            },&mut t);
            let expected=match fault {0=>"injected read failure",1|2=>"adjacency streamed chunk width mismatch",_=>"adjacency streamed source is non-Boolean"};
            assert_eq!(result.err().unwrap(),expected);assert_eq!(calls,failing_call);
            if failing_call<=chunks {assert_eq!(transcript_snapshot(&t),before);}
        }}
        let mut arbitrary=w.clone();arbitrary[0]=Fr::from(2u64);
        assert!(rel.prove(&arbitrary,&mut Transcript::new(b"field-domain")).is_ok());
        assert_eq!(rel.prove_streamed_reader(3,|chunk|Ok(arbitrary[chunk*8..(chunk+1)*8].to_vec()),
            &mut Transcript::new(b"field-domain")).err().unwrap(),"adjacency streamed source is non-Boolean");
        for b in [rel.input_log()+1,17] {
            assert!(rel.prove_streamed_reader(b,|_|panic!("invalid dimension must not read"),&mut Transcript::new(b"bad-width")).is_err());
        }
    }

    #[test]
    #[cfg(windows)]
    fn streamed_public_entry_rejects_packed_dimension_before_transcript() {
        use std::io::Write;
        let path=std::env::temp_dir().join(format!("adjacency-wrong-dimension-{}-{}.bits",
            std::process::id(),std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let mut file=std::fs::OpenOptions::new().write(true).create_new(true).open(&path).unwrap();
        file.write_all(&[0u8]).unwrap();drop(file);
        let source=PackedFile::open(&path,3).unwrap();let rel=relation(1);
        let mut t=Transcript::new(b"stream-public-dimension");let before=transcript_snapshot(&t);
        assert_eq!(rel.prove_streamed_boolean(&source,&mut t).err().unwrap(),
            "adjacency packed source dimension mismatch");
        assert_eq!(transcript_snapshot(&t),before);
        // Retain the tiny create-only fixture; no source or directory cleanup.
    }

    #[test]
    fn streamed_bad_endpoints_and_links_fail_before_transcript_mutation() {
        for n in [1,2,4] {
            let mut rel=relation(n);rel.header_bits=10;let original=boolean_input(&rel);
            let mut faults=vec![rel.parent_wires[0],((n-1)<<10)+rel.digest_wires[255]];
            faults.extend((1..n).map(|i|(i<<10)+rel.parent_wires[255]));
            for wire in faults {
                let mut w=original.clone();w[wire]=Fr::one()-w[wire];let mut t=Transcript::new(b"stream-bad-residual");
                let before=transcript_snapshot(&t);let mut calls=0;
                let result=rel.prove_streamed_reader(3,|chunk| {calls+=1;Ok(w[chunk*8..(chunk+1)*8].to_vec())},&mut t);
                assert_eq!(result.err().unwrap(),"nonzero adjacency residual");assert_eq!(calls,w.len()/8);
                assert_eq!(transcript_snapshot(&t),before);
            }
        }
    }

    #[test]
    fn compact_dense_stream_parity_and_exact_read_ledger() {
        for n in [1,2,4] {
            let rel=Relation::new_compact(n,[0x95;32],[0x63;32]).unwrap();
            assert_eq!(rel.input_log(),9+n.trailing_zeros() as usize);
            assert_eq!(rel.row_count(),512*n);
            let w=input(&rel);
            assert!(w.iter().all(|x|x.is_zero()||x.is_one()));
            assert!(nonzero(&rel.residuals(&w).unwrap()).is_empty());
            let mut dense_t=Transcript::new(b"compact-parity");
            let dense=rel.prove(&w,&mut dense_t).unwrap();
            let mut calls=0;let mut streamed_t=Transcript::new(b"compact-parity");
            let (proof,claim,stats)=rel.prove_streamed_reader(9,|header| {
                calls+=1;Ok(w[header*512..(header+1)*512].to_vec())
            },&mut streamed_t).unwrap();
            assert_eq!(proof,dense.0);assert_eq!(claim,dense.1);
            assert_eq!(gkr::encode_proof(&proof).unwrap(),gkr::encode_proof(&dense.0).unwrap());
            assert_eq!(transcript_snapshot(&streamed_t),transcript_snapshot(&dense_t));
            assert_eq!(stats.chunk_reads,22*n as u64);assert_eq!(calls,22*n);
            assert_eq!(stats.chunk_fields_max,512);assert_eq!(stats.transition_fields_max,3*n);
            let mut verify_t=Transcript::new(b"compact-parity");
            assert_eq!(rel.verify(&proof,&mut verify_t).unwrap(),claim);
            assert_eq!(transcript_snapshot(&verify_t),transcript_snapshot(&dense_t));
            let mut faults=vec![0,511+(n-1)*512];
            faults.extend((1..n).map(|header|header*512+255));
            for index in faults {
                let mut changed=w.clone();changed[index]=Fr::one()-changed[index];
                let mut before_t=Transcript::new(b"compact-fault");
                let before=transcript_snapshot(&before_t);
                assert!(nonzero(&rel.residuals(&changed).unwrap()).len()==1);
                assert_eq!(rel.prove_streamed_reader(9,|header|Ok(changed[header*512..(header+1)*512].to_vec()),
                    &mut before_t).err().unwrap(),"nonzero adjacency residual");
                assert_eq!(transcript_snapshot(&before_t),before);
            }
        }
        assert!(Relation::new_compact(3,[0;32],[0;32]).is_err());
    }

    #[test]
    fn compact_reader_rejects_wrong_width_value_and_error() {
        let rel=Relation::new_compact(1,[0;32],[0;32]).unwrap();
        let w=vec![Fr::zero();512];
        for fault in 0..4 {
            let mut t=Transcript::new(b"compact-reader-fault");
            let before=transcript_snapshot(&t);
            let result=rel.prove_streamed_reader(9,|_|match fault {
                0=>Err("reader failed".into()),
                1=>Ok(vec![Fr::zero();511]),
                2=>Ok(vec![Fr::zero();513]),
                _=>{let mut x=w.clone();x[77]=Fr::from(2u64);Ok(x)},
            },&mut t);
            let error=match fault {0=>"reader failed",1|2=>"adjacency streamed chunk width mismatch",
                _=>"adjacency streamed source is non-Boolean"};
            assert_eq!(result.err().unwrap(),error);
            assert_eq!(transcript_snapshot(&t),before);
        }
        assert!(rel.prove_streamed_reader(10,|_|panic!("invalid width must not read"),
            &mut Transcript::new(b"bad-width")).is_err());
        let two=Relation::new_compact(2,[0;32],[0;32]).unwrap();
        let mut arbitrary=vec![Fr::zero();1024];
        arbitrary[256+77]=Fr::from(3u64);
        arbitrary[512+77]=Fr::from(3u64);
        assert!(two.prove(&arbitrary,&mut Transcript::new(b"dense-field")).is_ok());
        assert_eq!(two.prove_streamed_reader(9,|header|Ok(arbitrary[header*512..(header+1)*512].to_vec()),
            &mut Transcript::new(b"boolean-field")).err().unwrap(),"adjacency streamed source is non-Boolean");
    }
}
