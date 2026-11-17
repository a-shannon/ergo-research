//! Literal-prefix Fiat-Shamir hashing; no digest replaces the accumulated prefix.
use ark_bn254::Fr;
use ark_ff::{BigInt, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use blake2::{Blake2b512, Digest};
use dory_pcs::backends::arkworks::{ArkFr, BN254};
use dory_pcs::primitives::{arithmetic::Group, serialization::Compress, DorySerialize};

const ATTEMPT_LIMIT: u64 = 4096;

#[derive(Clone)]
pub struct Transcript {
    state: Blake2b512,
    challenge_count: u64,
    raw_query_count: u64,
    bytes: u64,
}

fn frame(kind: u8, label: &[u8], data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(17 + label.len() + data.len());
    out.push(kind);
    out.extend_from_slice(&(label.len() as u64).to_le_bytes());
    out.extend_from_slice(label);
    out.extend_from_slice(&(data.len() as u64).to_le_bytes());
    out.extend_from_slice(data);
    out
}

fn candidate(digest: &[u8]) -> Option<Fr> {
    let mut limbs = [0u64; 4];
    for (limb, bytes) in limbs.iter_mut().zip(digest[..32].chunks_exact(8)) {
        *limb = u64::from_le_bytes(bytes.try_into().expect("eight bytes"));
    }
    limbs[3] &= 0x3fff_ffff_ffff_ffff; // BN254 scalar modulus has 254 bits.
    Fr::from_bigint(BigInt(limbs)).filter(|x| !x.is_zero())
}

impl Transcript {
    pub fn new(domain: &[u8]) -> Self {
        let mut value = Self {
            state: Blake2b512::new(), challenge_count: 0, raw_query_count: 0, bytes: 0,
        };
        value.absorb(0, b"protocol", b"gkr-dory-full-prefix-v1");
        value.absorb(0, b"domain", domain);
        value
    }

    fn absorb(&mut self, kind: u8, label: &[u8], data: &[u8]) {
        // Stream the same framing as `frame` without copying large circuit inputs.
        self.state.update([kind]);
        self.state.update((label.len() as u64).to_le_bytes());
        self.state.update(label);
        self.state.update((data.len() as u64).to_le_bytes());
        self.state.update(data);
        self.bytes = self.bytes.checked_add((17 + label.len() + data.len()) as u64)
            .expect("transcript length overflow");
    }

    pub fn append_bytes(&mut self, label: &[u8], bytes: &[u8]) {
        self.absorb(1, label, bytes);
    }

    pub fn append_u64(&mut self, label: &[u8], value: u64) {
        self.absorb(5, label, &value.to_le_bytes());
    }

    pub fn append_scalar(&mut self, label: &[u8], value: &Fr) {
        let mut bytes = Vec::with_capacity(32);
        value.serialize_compressed(&mut bytes).expect("Vec serialization");
        self.absorb(2, label, &bytes);
    }

    pub fn try_challenge_scalar(&mut self, label: &[u8]) -> Result<Fr, String> {
        let counter = self.challenge_count;
        for attempt in 0..ATTEMPT_LIMIT {
            let mut query = Vec::with_capacity(16);
            query.extend_from_slice(&counter.to_le_bytes());
            query.extend_from_slice(&attempt.to_le_bytes());
            let mut hasher = self.state.clone();
            hasher.update(frame(0x30, label, &query));
            let digest = hasher.finalize();
            self.raw_query_count = self.raw_query_count.checked_add(1)
                .ok_or("raw query counter overflow")?;
            if let Some(value) = candidate(&digest) {
                value.serialize_compressed(&mut query).map_err(|e| e.to_string())?;
                self.absorb(0x40, label, &query);
                self.challenge_count = counter.checked_add(1).ok_or("challenge counter overflow")?;
                return Ok(value);
            }
        }
        Err("nonzero field rejection sampler exhausted 4096 attempts".into())
    }

    pub fn challenge_scalar(&mut self, label: &[u8]) -> Fr {
        // The vendor trait cannot return errors. Exhaustion aborts; never accepts.
        self.try_challenge_scalar(label).expect("Fiat-Shamir sampling failed closed")
    }

    pub fn raw_queries(&self) -> u64 { self.raw_query_count }
    pub fn challenges(&self) -> u64 { self.challenge_count }
    pub fn bytes_absorbed(&self) -> u64 { self.bytes }
}

impl dory_pcs::primitives::transcript::Transcript for Transcript {
    type Curve = BN254;
    fn append_bytes(&mut self, label: &[u8], bytes: &[u8]) {
        Transcript::append_bytes(self, label, bytes);
    }
    fn append_field(&mut self, label: &[u8], x: &ArkFr) {
        self.append_scalar(label, &x.0);
    }
    fn append_group<G: Group>(&mut self, label: &[u8], g: &G) {
        let mut bytes = Vec::new();
        g.serialize_with_mode(&mut bytes, Compress::Yes).expect("Vec serialization");
        self.absorb(4, label, &bytes);
    }
    fn append_serde<S: DorySerialize>(&mut self, label: &[u8], value: &S) {
        let mut bytes = Vec::new();
        value.serialize_with_mode(&mut bytes, Compress::Yes).expect("Vec serialization");
        self.absorb(3, label, &bytes);
    }
    fn challenge_scalar(&mut self, label: &[u8]) -> ArkFr {
        ArkFr(Transcript::challenge_scalar(self, label))
    }
    fn reset(&mut self, domain: &[u8]) { *self = Self::new(domain); }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn incremental_equals_literal_prefix_reference() {
        let mut transcript = Transcript::new(b"parity");
        let mut bytes = frame(0, b"protocol", b"gkr-dory-full-prefix-v1");
        bytes.extend(frame(0, b"domain", b"parity"));
        let payload = vec![0x5a; 1_000_003];
        transcript.append_bytes(b"circuit", &payload);
        bytes.extend(frame(1, b"circuit", &payload));
        let mut attempts = 0;
        for counter in 0u64..20 {
            let scalar = Fr::from(counter + 19);
            transcript.append_scalar(b"message", &scalar);
            let mut encoded = Vec::new();
            scalar.serialize_compressed(&mut encoded).unwrap();
            bytes.extend(frame(2, b"message", &encoded));
            let expected = (0..ATTEMPT_LIMIT).find_map(|attempt| {
                let mut query = counter.to_le_bytes().to_vec();
                query.extend(attempt.to_le_bytes());
                let mut literal = bytes.clone();
                literal.extend(frame(0x30, b"round", &query));
                attempts += 1;
                candidate(&Blake2b512::digest(&literal)).map(|value| {
                    value.serialize_compressed(&mut query).unwrap();
                    bytes.extend(frame(0x40, b"round", &query));
                    value
                })
            }).unwrap();
            assert_eq!(transcript.challenge_scalar(b"round"), expected);
        }
        assert_eq!(transcript.raw_queries(), attempts);
        assert_eq!(transcript.bytes_absorbed(), bytes.len() as u64);
    }

    #[test]
    fn framing_and_domain_are_distinct() {
        let mut a = Transcript::new(b"A");
        let mut b = Transcript::new(b"A");
        a.append_bytes(b"ab", b"c");
        b.append_bytes(b"a", b"bc");
        assert_ne!(a.challenge_scalar(b"x"), b.challenge_scalar(b"x"));
        assert_ne!(Transcript::new(b"A").challenge_scalar(b"x"),
                   Transcript::new(b"B").challenge_scalar(b"x"));
        assert_eq!(candidate(&[0u8; 64]), None);
        assert_eq!(candidate(&[255u8; 64]), None);
    }
}
