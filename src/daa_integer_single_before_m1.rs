//! Exact pre-extension single-A1 compiler body, retained only for regression.
use super::*;

pub(crate) fn compile_before_m1(epoch:Epoch,q:&BigUint,input:Inputs,materialize:bool)->Result<Compiled,String>{
    if q.bits()>256 || q.is_zero(){return Err("invalid descriptor Q".into());}
    let mut b=Builder::new(materialize);
    let nbits: [usize;32]=b.bits_u64(input.nbits as u64,32).try_into().map_err(|_|"nbits map")?;
    let start:[usize;64]=b.bits_u64(input.start_timestamp as u64,64).try_into().map_err(|_|"start map")?;
    let end:[usize;64]=b.bits_u64(input.end_timestamp as u64,64).try_into().map_err(|_|"end map")?;
    let external=ExternalBits{nbits,start_timestamp:start,end_timestamp:end};
    let d=decode_constraints(&mut b,&external.nbits,q);
    let (delta,magnitude)=signed_difference(&mut b,&external.start_timestamp,&external.end_timestamp);
    let numerator=constant_numerator(&mut b,&d,epoch);
    let (quotient,remainder,quotient_negative,remainder_negative)=quotient_product(&mut b,&numerator,&magnitude,delta[63],epoch);
    // Signed quotient follows the wrapped signed denominator unless q=0.
    let q_nonzero=b.nonzero_unasserted(&quotient);
    b.row(vec![Builder::linear(quotient_negative,Fr::one()),Builder::product(delta[63],q_nonzero,-Fr::one())]);
    let output=OutputBits{decoded_difficulty:d,wrapped_delta:delta,denominator_magnitude:magnitude,
        numerator,quotient_magnitude:quotient,quotient_negative,remainder_magnitude:remainder,remainder_negative};
    b.pad();let (count,circuit,witness,subtract_traces,carry_wires)=b.finish(Categories{nbits:32,timestamps:128,instances:1,numerator_width:epoch.numerator_bits()})?;
    Ok(Compiled{count,external,output,circuit,witness,subtract_traces,carry_wires})
}

#[test]
fn empty_continuation_preserves_exact_single_a1() {
    let q = crate::daa_count::q();
    let cases = [
        Inputs { nbits: 0x0601_1765, start_timestamp: 1_561_986_131_991, end_timestamp: 1_561_993_105_670 },
        Inputs { nbits: 0x0300_0001, start_timestamp: 0, end_timestamp: 122_880_001 },
        Inputs { nbits: 0x0300_0001, start_timestamp: 1, end_timestamp: 0 },
        Inputs { nbits: 0x0300_0001, start_timestamp: -1, end_timestamp: 0 },
        Inputs { nbits: 0x0300_0001, start_timestamp: i64::MAX, end_timestamp: i64::MIN },
    ];
    for epoch in [Epoch::Legacy, Epoch::Eip] {
        for input in cases {
            for materialize in [false, true] {
                let old = compile_before_m1(epoch, &q, input, materialize).unwrap();
                let current = super::compile(epoch, &q, input, materialize).unwrap();
                assert_eq!(format!("{:?}", old.count), format!("{:?}", current.count));
                assert_eq!(old.circuit, current.circuit);
                assert_eq!(old.witness, current.witness);
                assert_eq!(old.carry_wires, current.carry_wires);
                assert_eq!(format!("{:?}", old.external), format!("{:?}", current.external));
                assert_eq!(format!("{:?}", old.output), format!("{:?}", current.output));
                assert_eq!(format!("{:?}", old.subtract_traces), format!("{:?}", current.subtract_traces));
            }
        }
    }
    for invalid_q in [BigUint::zero(), BigUint::one() << 256usize] {
        let old = compile_before_m1(Epoch::Legacy, &invalid_q, cases[0], true).err();
        let current = super::compile(Epoch::Legacy, &invalid_q, cases[0], true).err();
        assert_eq!(old.as_deref(), Some("invalid descriptor Q"));
        assert_eq!(old, current);
    }
    println!("old single-A1 body differential PASS: 2 epochs x 5 assignments x 2 modes; exact circuit, witness, Count, handles, traces, carries and invalid-Q rejection");
}
