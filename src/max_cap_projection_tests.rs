// Bounded TEST-only owner0 suffix-MAX projection. Foreign PCS is not foreign MAX validity.
mod max_cap_projection_tests {
    use super::*;
    use crate::certified_modern_cap::{self as cap, Statement};
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
    use num_bigint::{BigInt, BigUint};
    use std::{cell::Cell, ops::Range};

    include!("max_envelope_guard_tests.rs");

    const DOMAIN: &[u8] = b"max-to-elementary-cap-n3-local-v1";
    const ROLE: &[u8] = b"owner0-suffix-MAX224-and-next32";
    const KEY: &[u8] = include_bytes!("../fixtures/verifier-keys-v1/log22.vk");
    const FOREIGN_DIGEST: &str = "6A4C720D361D1AB272528D01D4295BDA949DA3C605243A21C08ADB118190E3E7";

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Bank { Maximum, Difficulty }
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Descriptor {
        n: usize, c: usize, slot_log: usize, input_log: usize, owner: usize,
        first: usize, last: usize, base: usize, width: usize, selected: usize,
        tail: usize, lsb: bool, bank: Bank,
    }
    const DESC: Descriptor = Descriptor {
        n: 3, c: 4, slot_log: 2, input_log: 22, owner: 0, first: 2, last: 3,
        base: 999424, width: 256, selected: 224, tail: 32, lsb: true,
        bank: Bank::Maximum,
    };
    fn validate(d: Descriptor) -> Result<(), String> {
        if d != DESC { return Err("code-owned MAX descriptor".into()); }
        if std::mem::size_of::<usize>() != 8 || d.base % 256 != 0
            || d.selected + d.tail != d.width || d.base + d.width > 1usize << 20usize
            || d.first.checked_sub(2) != Some(d.owner) || d.last != d.n {
            return Err("MAX projection geometry".into());
        }
        Ok(())
    }
    fn before_read<T>(d: Descriptor, f: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
        validate(d)?; f()
    }
    fn bind_descriptor(t: &mut Transcript, d: Descriptor) {
        for n in [d.n, d.c, d.slot_log, d.input_log, d.owner, d.first, d.last,
            d.base, d.width, d.selected, d.tail, usize::from(d.lsb)] {
            t.append_u64(b"MAX-descriptor", n as u64);
        }
        t.append_bytes(b"MAX-bank", b"suffix-maximum");
    }
    fn point(d: Descriptor, rho: &[Fr]) -> Result<Vec<Fr>, String> {
        validate(d)?;
        if rho.len() != 8 { return Err("MAX rho dimension".into()); }
        let g = d.owner * (1usize << 20usize) + d.base;
        let mut out = rho.to_vec();
        for j in 8usize..22usize { out.push(Fr::from(((g >> j) & 1usize) as u64)); }
        assert_eq!(out.len(), 22); Ok(out)
    }
    fn read_block(source: &PackedFile, d: Descriptor) -> Result<[bool; 256], String> {
        before_read(d, || {
            if source.input_len() != 1usize << 22usize { return Err("MAX source dimension".into()); }
            let g = d.owner * (1usize << 20usize) + d.base;
            let values = source.read_copy(256, g / 256)?;
            if values.len() != 256 || values.iter().any(|x| !x.is_zero() && !x.is_one()) {
                return Err("MAX block Boolean framing".into());
            }
            Ok(std::array::from_fn(|i| values[i].is_one()))
        })
    }
    fn packed_bits(bytes: &[u8], start: usize) -> [bool; 256] {
        assert!(start + 256 <= bytes.len() * 8);
        std::array::from_fn(|i| (bytes[(start + i) / 8] >> ((start + i) % 8)) & 1 == 1)
    }
    fn number(bits: &[bool]) -> BigUint {
        bits.iter().enumerate().fold(BigUint::from(0u8), |a, (i, bit)| {
            if *bit { a + (BigUint::from(1u8) << i) } else { a }
        })
    }
    fn bit_fields(bits: &[bool]) -> Vec<Fr> {
        bits.iter().map(|b| Fr::from(u64::from(*b))).collect()
    }
    fn expected_block(d2: &BigUint, d3: &BigUint) -> [bool; 256] {
        let maximum = std::cmp::max(d2, d3);
        std::array::from_fn(|i| if i < 224 { maximum.bit(i as u64) } else { d3.bit((i - 224) as u64) })
    }

    struct Reference {
        p: BigUint, r: BigUint, e: usize, q: BigUint, prev: BigUint,
        hi: BigUint, low: BigUint, positive: BigUint,
    }
    fn reference(m: &BigUint) -> Result<Reference, String> {
        if m.is_zero() || m.bits() > 224 { return Err("reference positive MAX224".into()); }
        let integer = BigInt::from(m.clone());
        let three = &integer * BigInt::from(3u8);
        let p = &three / BigInt::from(2u8);
        let r = &three - &p * BigInt::from(2u8);
        let mut q = BigInt::from(1u8); let mut e = 0usize;
        while q < p {
            q *= BigInt::from(2u8); e += 1;
            if e > 64 { return Err("reference cap coverage".into()); }
        }
        let prev = if e == 0 { BigInt::from(0u8) } else { &q / BigInt::from(2u8) };
        let unsigned = |x: BigInt| x.to_biguint().ok_or_else(|| "reference negative rail".to_string());
        Ok(Reference { p: unsigned(p.clone())?, r: unsigned(r)?, e,
            q: unsigned(q.clone())?, prev: unsigned(prev.clone())?, hi: unsigned(&q - &p)?,
            low: unsigned(&p - &prev - BigInt::from(1u8))?, positive: unsigned(integer - BigInt::from(1u8))? })
    }
    fn write_bits(x: &mut [Fr], rail: Range<usize>, n: &BigUint) {
        assert!(n.bits() <= rail.len() as u64);
        for (i, w) in rail.enumerate() { x[w] = Fr::from(u64::from(n.bit(i as u64))); }
    }
    struct FixedX { values: Vec<Fr> }
    impl FixedX {
        fn from_authenticated_bits(bits: &[bool; 256]) -> Result<Self, String> {
            cap::bounds(); let m = number(&bits[..224]); let r = reference(&m)?;
            let mut values = vec![Fr::zero(); 2048]; assert_eq!(values.capacity(), 2048);
            // Literal rails and independent integer arithmetic; no producer/layout/scalar helpers.
            write_bits(&mut values, 1..225, &m); write_bits(&mut values, 225..449, &m);
            write_bits(&mut values, 449..674, &r.p); write_bits(&mut values, 674..675, &r.r);
            values[675 + r.e] = Fr::one(); write_bits(&mut values, 740..805, &r.q);
            write_bits(&mut values, 805..869, &r.prev); write_bits(&mut values, 869..934, &r.hi);
            write_bits(&mut values, 934..1159, &r.low); write_bits(&mut values, 1159..1383, &r.positive);
            assert!(values[1383..].iter().all(Zero::is_zero)); Ok(Self { values })
        }
        fn authenticate(&self, claim: &InputClaim) -> Result<(), String> {
            if claim.point.len() != 11 { return Err("MAX cap terminal dimension".into()); }
            if gkr::mle(&self.values, &claim.point).map_err(|e| e.to_string())? != claim.value {
                return Err("MAX cap terminal known-X".into());
            }
            Ok(())
        }
    }
    #[derive(Clone)]
    struct Declaration { descriptor: Descriptor, block: [bool; 256], q: BigUint }
    impl Declaration {
        fn new(block: [bool; 256], q: BigUint) -> Result<Self, String> {
            reference(&number(&block[..224]))?;
            if q.is_zero() || q > BigUint::from(1u8) << 64usize { return Err("MAX public q profile".into()); }
            Ok(Self { descriptor: DESC, block, q })
        }
        fn statement(&self) -> Result<Statement, String> {
            validate(self.descriptor)?; Statement::new(&number(&self.block[..224]), &self.q)
        }
        fn q_bits(&self) -> Vec<u8> { (0u64..65u64).map(|i| u8::from(self.q.bit(i))).collect() }
    }
    struct MaxBinding { public: Vec<u8>, corpus: [u8; 32], key_id: [u8; 32], commitment: Vec<u8> }
    impl MaxBinding {
        fn new(public: &Public, key: &verifier_key::AdmittedVerifierKey, commitment: &[u8]) -> Result<Self, String> {
            if public.headers != 3 || key.log_n() != 22 { return Err("MAX N3/key profile".into()); }
            pcs::decode_commitment(commitment)?;
            let public = public.bytes()?; let corpus = Blake2b::<U32>::digest(&public).into();
            Ok(Self { public, corpus, key_id: *key.id(), commitment: commitment.to_vec() })
        }
        fn cap_bind(&self, declaration: &Declaration, t: &mut Transcript) {
            t.append_bytes(b"MAX-cap-contract", b"q-of-authenticated-suffix-MAX-local-v1");
            t.append_bytes(b"MAX-public", &self.public); t.append_bytes(b"MAX-corpus", &self.corpus);
            t.append_bytes(b"MAX-key", &self.key_id); t.append_bytes(b"MAX-commitment", &self.commitment);
            bind_descriptor(t, declaration.descriptor);
            for n in [2048u64, 4096u64, 6549u64] { t.append_u64(b"MAX-cap-layout", n); }
            for b in &declaration.block[..224] { t.append_u64(b"MAX-cap-source-bit", u64::from(*b)); }
            t.append_bytes(b"MAX-cap-public-q", &declaration.q_bits());
        }
    }
    // Only this constructor grants the original MAX-packet gate. Foreign PCS never uses it.
    struct VerifiedMax { binding: MaxBinding }
    impl VerifiedMax {
        fn admit(public: &Public, artifact: &Artifact, key: &verifier_key::AdmittedVerifierKey) -> Result<Self, String> {
            Consumer::new(public)?.verify(artifact, key).map_err(|e| format!("original MAX packet: {e:?}"))?;
            Ok(Self { binding: MaxBinding::new(public, key, &artifact.commitment)? })
        }
        fn consume(&self, declaration: &Declaration, opening: &[u8], cap_proof: &[u8],
            key: &verifier_key::AdmittedVerifierKey) -> Result<(InputClaim, Transcript), String> {
            let base = verify_projection(&self.binding, declaration, opening, key, Fault::None)?;
            verify_cap(&self.binding, declaration, cap_proof, &base)
        }
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Fault { None, MissingBlock, LateBlock, MissingQ, LateQ, Domain, Role,
        Public, Corpus, Key, Commitment, RhoLabel, RhoOrder }
    const FS_FAULTS: [Fault; 12] = [Fault::MissingBlock, Fault::LateBlock, Fault::MissingQ,
        Fault::LateQ, Fault::Domain, Fault::Role, Fault::Public, Fault::Corpus, Fault::Key,
        Fault::Commitment, Fault::RhoLabel, Fault::RhoOrder];
    fn projection(binding: &MaxBinding, declaration: &Declaration, fault: Fault)
        -> Result<(Transcript, Vec<Fr>, Fr), String> {
        validate(declaration.descriptor)?; declaration.statement()?;
        let mut t = Transcript::new(if fault == Fault::Domain { b"counterfactual-MAX-domain" } else { DOMAIN });
        let mut public = binding.public.clone(); let mut corpus = binding.corpus;
        let mut key = binding.key_id; let mut commitment = binding.commitment.clone();
        if fault == Fault::Public { public[0] ^= 1; }
        if fault == Fault::Corpus { corpus[0] ^= 1; }
        if fault == Fault::Key { key[0] ^= 1; }
        if fault == Fault::Commitment { commitment[0] ^= 1; }
        t.append_bytes(b"MAX-public", &public); t.append_bytes(b"MAX-corpus", &corpus);
        t.append_bytes(b"MAX-key", &key); t.append_bytes(b"MAX-commitment", &commitment);
        t.append_bytes(b"MAX-role", if fault == Fault::Role { b"counterfactual-MAX-role" } else { ROLE });
        bind_descriptor(&mut t, declaration.descriptor);
        let block = declaration.block.map(u8::from); let q = declaration.q_bits();
        if !matches!(fault, Fault::MissingBlock | Fault::LateBlock) { t.append_bytes(b"MAX-declared-block", &block); }
        if !matches!(fault, Fault::MissingQ | Fault::LateQ) { t.append_bytes(b"MAX-public-q", &q); }
        let mut rho = Vec::with_capacity(8);
        for i in 0usize..8usize {
            let mut label = b"MAX-rho-LSB-".to_vec(); label.push(i as u8);
            if fault == Fault::RhoLabel && i == 0 { label.push(0); }
            rho.push(t.challenge_scalar(&label));
        }
        if fault == Fault::LateBlock { t.append_bytes(b"MAX-declared-block", &block); }
        if fault == Fault::LateQ { t.append_bytes(b"MAX-public-q", &q); }
        if fault == Fault::RhoOrder { rho.reverse(); }
        let point = point(declaration.descriptor, &rho)?;
        let value = gkr::mle(&bit_fields(&declaration.block), &rho).map_err(|e| e.to_string())?;
        assert_eq!(t.challenges(), 8); Ok((t, point, value))
    }
    fn verify_projection(binding: &MaxBinding, declaration: &Declaration, bytes: &[u8],
        key: &verifier_key::AdmittedVerifierKey, fault: Fault) -> Result<Transcript, String> {
        if key.log_n() != 22 || key.id() != &binding.key_id { return Err("MAX admitted key mismatch".into()); }
        let (mut t, point, value) = projection(binding, declaration, fault)?;
        let proof = pcs::decode_proof(bytes, 22)?;
        // The commitment, point and claimed scalar are code-owned expected inputs, never proof advice.
        pcs::verify_admitted(pcs::decode_commitment(&binding.commitment)?, value, &point, &proof, key, &mut t)?;
        Ok(t)
    }
    fn verify_cap(binding: &MaxBinding, declaration: &Declaration, bytes: &[u8], base: &Transcript)
        -> Result<(InputClaim, Transcript), String> {
        let stmt = declaration.statement()?; let circuit = cap::materialize(&stmt);
        let proof = sparse::decode_proof(&circuit, 0, bytes)?;
        let mut t = base.clone(); let start = t.challenges();
        let claim = gkr::verify_with_wiring(&[11], 4096, &proof, &mut t,
            |t| binding.cap_bind(declaration, t), |layer, r, u, v| {
                if layer != 0 { return Err(GkrError::ProofLayerCount); }
                cap::coefficients(&stmt, r, u, v)
            }).map_err(|e| e.to_string())?;
        FixedX::from_authenticated_bits(&declaration.block)?.authenticate(&claim)?;
        if t.challenges() != start + 35 { return Err("MAX cap challenge delta".into()); }
        Ok((claim, t))
    }
    fn prove_cap(binding: &MaxBinding, declaration: &Declaration, base: &Transcript)
        -> Result<(Vec<u8>, InputClaim, Transcript), String> {
        let stmt = declaration.statement()?; let circuit = cap::materialize(&stmt);
        let producer = cap::producer(&number(&declaration.block[..224]))?;
        let fixed = FixedX::from_authenticated_bits(&declaration.block)?;
        assert_eq!(producer, fixed.values);
        assert!(cap::residuals(&circuit, &producer).iter().all(Zero::is_zero));
        let mut t = base.clone(); let start = t.challenges();
        let (proof, claim) = sparse::prove_with_binding(&circuit, &producer, 0, &mut t,
            |t| binding.cap_bind(declaration, t)).map_err(|e| e.to_string())?;
        let bytes = gkr::encode_proof(&proof)?; assert_eq!(bytes.len(), 2560);
        assert_eq!(sparse::decode_proof(&circuit, 0, &bytes)?, proof);
        assert_eq!(t.challenges(), start + 35); Ok((bytes, claim, t))
    }

    struct Fixture { public: Public, artifact: Artifact, source: PackedFile,
        bytes: Vec<u8>, block: [bool; 256], q: BigUint }
    fn fixture() -> Result<Fixture, String> {
        cap::bounds(); validate(DESC)?; check_native_bundle()?;
        let dir = baseline_directory()?; let public = Public::native(3)?;
        let artifact = baseline_packet(&dir, &public)?;
        let source = PackedFile::open(dir.join("witness.bits"), 22)?;
        // Recheck the exact bytes after acquiring the immutable source handle.
        let bytes = pinned_bytes(&dir.join("witness.bits"), 524288, PACKET_FILES[10].2)?;
        let input = before_read(DESC, || native_input(&public))?;
        let d2 = crate::work_tree_work::native_decode(input.compact_n_bits(2)?)?;
        let d3 = crate::work_tree_work::native_decode(input.compact_n_bits(3)?)?;
        assert!(!d2.is_zero() && !d3.is_zero() && d2.bits() <= 224 && d3.bits() <= 224);
        let block = read_block(&source, DESC)?;
        assert_eq!(block, expected_block(&d2, &d3)); assert_eq!(block, packed_bits(&bytes, DESC.base));
        assert_eq!(number(&block[..224]), BigUint::from(1199990374400u64));
        assert_eq!(number(&block[224..]), BigUint::from(1694498816u64));
        let q = reference(&number(&block[..224]))?.q; assert_eq!(q, BigUint::from(2199023255552u64));
        Ok(Fixture { public, artifact, source, bytes, block, q })
    }
    fn geometry_controls() {
        let reads = Cell::new(0usize); let challenges = Cell::new(0usize); let pcs_calls = Cell::new(0usize);
        for axis in 0usize..13usize {
            let mut d = DESC;
            match axis { 0 => d.n += 1, 1 => d.c += 1, 2 => d.slot_log += 1, 3 => d.input_log += 1,
                4 => d.owner += 1, 5 => d.first += 1, 6 => d.last += 1, 7 => d.base += 256,
                8 => d.width /= 2, 9 => d.selected -= 1, 10 => d.tail -= 1,
                11 => d.lsb = false, _ => d.bank = Bank::Difficulty }
            assert_eq!(before_read(d, || { reads.set(reads.get() + 1); Ok(BigUint::from(1199990374400u64)) }).unwrap_err(), "code-owned MAX descriptor");
            assert!(before_read(d, || { challenges.set(challenges.get() + 1); Ok(()) }).is_err());
            assert!(before_read(d, || { pcs_calls.set(pcs_calls.get() + 1); Ok(()) }).is_err());
            assert_eq!((reads.get(), challenges.get(), pcs_calls.get()), (0, 0, 0));
        }
        assert_eq!(point(DESC, &[Fr::one(); 7]).unwrap_err(), "MAX rho dimension");
        assert!(Public::native(4).is_err());
    }
    // Compact N4 model evaluated against the actual suffix emitter, never an N4 packet.
    struct N4Witness {
        d: [BigUint; 4], m: [BigUint; 4], next: [BigUint; 4],
        delta: [BigUint; 4], selector: [bool; 4],
    }
    impl N4Witness {
        fn canonical(values: [u64; 3]) -> Self {
            let d = std::array::from_fn(|i| BigUint::from(if i < 3 { values[i] } else { 0u64 }));
            let mut m = std::array::from_fn(|_| BigUint::from(0u8));
            let mut next = std::array::from_fn(|_| BigUint::from(0u8));
            let mut delta = std::array::from_fn(|_| BigUint::from(0u8));
            let mut selector = [false; 4];
            for owner in (0usize..3usize).rev() {
                next[owner] = m[owner + 1].clone();
                selector[owner] = d[owner] < next[owner];
                delta[owner] = if selector[owner] {
                    &d[owner] + (BigUint::from(1u8) << 224usize) - &next[owner]
                } else { &d[owner] - &next[owner] };
                m[owner] = std::cmp::max(&d[owner], &next[owner]).clone();
            }
            Self { d, m, next, delta, selector }
        }
        fn wire(&self, index: usize) -> Result<Fr, String> {
            if index >= 4usize << 20usize { return Err("N4 compact wire bound".into()); }
            let owner = index >> 20usize; let local = index & ((1usize << 20usize) - 1);
            if local == 0 { return Ok(Fr::zero()); }
            let value = if (987674usize..987898usize).contains(&local) {
                self.d[owner].bit((local - 987674) as u64)
            } else if (999424usize..999648usize).contains(&local) {
                self.m[owner].bit((local - 999424) as u64)
            } else if (999648usize..999872usize).contains(&local) {
                self.next[owner].bit((local - 999648) as u64)
            } else if (999872usize..1000096usize).contains(&local) {
                self.delta[owner].bit((local - 999872) as u64)
            } else if local == 1000096 { self.selector[owner] }
            else { return Err("N4 unexpected compact wire".into()); };
            Ok(Fr::from(u64::from(value)))
        }
        fn actual_rows(&self) -> Result<Vec<Fr>, String> {
            let layout = crate::suffix_max::Layout::new(4, 4, 999424)?;
            assert_eq!((layout.input_log(), layout.row_count(), layout.term_count()), (22, 8192, 8743));
            let mut residuals = vec![Fr::zero(); 8192]; let mut count = 0usize;
            for (owner, expected) in [2242usize, 2690usize, 2690usize, 1121usize].into_iter().enumerate() {
                let emitted = layout.emit_owner(owner, |term| {
                    if term.row >= 8192 { return Err("N4 emitted row bound".into()); }
                    let gate = term.gate; let left = self.wire(gate.left)?; let right = self.wire(gate.right)?;
                    residuals[term.row] += gate.c0 + gate.c1 * left + gate.c2 * right + gate.c3 * left * right;
                    Ok(())
                })?;
                assert_eq!(emitted, expected); count += emitted;
            }
            assert_eq!(count, 8743); Ok(residuals)
        }
    }
    fn weighted_rows(rows: &[Fr], start: usize) -> Fr {
        let mut weight = Fr::one(); let mut result = Fr::zero();
        for bit in 0usize..224usize { result += rows[start + bit] * weight; weight += weight; }
        result
    }
    fn isolate_n4_rows(rows: &[Fr], affected: Range<usize>, expected: Fr) {
        assert!(rows[..affected.start].iter().all(Zero::is_zero));
        assert!(rows[affected.end..].iter().all(Zero::is_zero));
        assert!(rows[affected.clone()].iter().any(|x| !x.is_zero()));
        assert_eq!(weighted_rows(rows, affected.start), expected);
    }
    fn n4_emitted_controls() -> Result<(), String> {
        let mut witness = N4Witness::canonical([3u64, 9u64, 5u64]);
        assert_eq!(witness.m, [9u64, 9, 5, 0].map(BigUint::from));
        assert_eq!(witness.next, [9u64, 5, 0, 0].map(BigUint::from));
        assert!(witness.actual_rows()?.iter().all(Zero::is_zero));
        assert_eq!(reference(&witness.m[0])?.q, BigUint::from(16u8));
        // Endpoint-only owner0 still satisfies its Boolean, compare and select rows.
        // The actual owner1 N0=M1 import rows must reject it, including their bit weights.
        witness.m[0] = BigUint::from(5u8); witness.next[0] = BigUint::from(5u8);
        witness.delta[0] = (BigUint::from(1u8) << 224usize) - BigUint::from(2u8);
        witness.selector[0] = true;
        assert_eq!(reference(&witness.m[0])?.q, BigUint::from(8u8));
        isolate_n4_rows(&witness.actual_rows()?, 2048 + 898..2048 + 1122, -Fr::from(4u64));
        // Omit the start while retaining its native D: only owner0 select rows fail.
        let mut start = N4Witness::canonical([11u64, 9u64, 5u64]);
        assert!(start.actual_rows()?.iter().all(Zero::is_zero)); assert_eq!(start.m[0], BigUint::from(11u8));
        start.m[0] = BigUint::from(9u8);
        isolate_n4_rows(&start.actual_rows()?, 674..898, -Fr::from(2u64));
        // Omit the end from preceding suffixes: owner2 N1=M2 imports reject.
        let mut end = N4Witness::canonical([3u64, 9u64, 12u64]);
        assert!(end.actual_rows()?.iter().all(Zero::is_zero)); assert_eq!(end.m[0], BigUint::from(12u8));
        end.m[0] = BigUint::from(9u8); end.next[0] = BigUint::from(9u8);
        end.delta[0] = (BigUint::from(1u8) << 224usize) - BigUint::from(6u8); end.selector[0] = true;
        end.m[1] = BigUint::from(9u8); end.next[1] = BigUint::from(0u8);
        end.delta[1] = BigUint::from(9u8); end.selector[1] = false;
        isolate_n4_rows(&end.actual_rows()?, 4096 + 898..4096 + 1122, -Fr::from(12u64));
        assert!(Public::native(4).is_err()); Ok(())
    }
    fn pure_controls(f: &Fixture, binding: &MaxBinding, declaration: &Declaration) -> Result<(), String> {
        geometry_controls(); let m = number(&f.block[..224]); let r = reference(&m)?;
        assert_eq!(cap::scalar(&m)?, r.q);
        let fixed = FixedX::from_authenticated_bits(&f.block)?; let producer = cap::producer(&m)?;
        assert_eq!(producer, fixed.values); assert_eq!(fixed.values.capacity(), 2048);
        let stmt = declaration.statement()?; let circuit = cap::materialize(&stmt);
        assert_eq!((cap::LIVE, circuit.input_len, circuit.row_count, circuit.terms.len()), (1383, 2048, 4096, 6549));
        assert!(cap::residuals(&circuit, &fixed.values).iter().all(Zero::is_zero));
        let rho: Vec<Fr> = (2u64..10u64).map(Fr::from).collect(); let p = point(DESC, &rho)?;
        assert_eq!(&p[..8], rho.as_slice());
        for j in 8usize..22usize { assert_eq!(p[j], Fr::from(((DESC.base >> j) & 1usize) as u64)); }
        let fields = bit_fields(&f.block); let value = gkr::mle(&fields, &rho).map_err(|e| e.to_string())?;
        for bit in 0usize..256usize {
            let weight = cap::eq_at(&rho, bit); assert!(!weight.is_zero());
            let mut changed = fields.clone(); let previous = changed[bit]; changed[bit] = Fr::one() - previous;
            assert_eq!(gkr::mle(&changed, &rho).map_err(|e| e.to_string())? - value,
                (Fr::one() - previous - previous) * weight);
            assert_ne!(changed[bit], previous);
        }
        let mut zero_tail = fields.clone(); zero_tail[224..].fill(Fr::zero());
        assert_ne!(gkr::mle(&zero_tail, &rho).map_err(|e| e.to_string())?, value);
        let mut reversed = f.block; reversed.reverse(); assert_ne!(reversed, f.block);
        assert_ne!(packed_bits(&f.bytes, 987674), f.block); // D is not the suffix-M bank.
        let (canonical, canonical_point, _) = projection(binding, declaration, Fault::None)?;
        for fault in FS_FAULTS {
            let (mut t, p, _) = projection(binding, declaration, fault)?;
            let mut positive = canonical.clone();
            assert!(p != canonical_point || t.challenge_scalar(b"binding-control") != positive.challenge_scalar(b"binding-control"), "{fault:?}");
        }
        for (wire, group) in [(1usize, "input-anchors"), (225, "aliases"), (740, "q-anchors")] {
            let mut x = fixed.values.clone(); x[wire] = Fr::one() - x[wire];
            assert!(cap::group(group).any(|row| !cap::residuals(&circuit, &x)[row].is_zero()), "{group}");
        }
        n4_emitted_controls()?;
        Ok(())
    }
    #[test]
    fn fixed_bank_and_bindings() {
        let f = fixture().unwrap(); let key = verifier_key::admit(22, KEY).unwrap();
        let binding = MaxBinding::new(&f.public, &key, &f.artifact.commitment).unwrap();
        let declaration = Declaration::new(f.block, f.q.clone()).unwrap();
        pure_controls(&f, &binding, &declaration).unwrap();
    }

    fn recovery_guard(setup: &pcs::Setup, key: &verifier_key::AdmittedVerifierKey,
        verifier_bytes: &[u8]) -> Result<(), String> {
        if setup.log_n != 22 || key.log_n() != 22 || setup.id != *key.id() { return Err("MAX setup reproduction".into()); }
        if verifier_bytes != KEY { return Err("MAX verifier bytes reproduction".into()); } Ok(())
    }
    fn commitment_guard(actual: &[u8], expected: &[u8]) -> Result<(), String> {
        if actual.len() != 384 || actual != expected { return Err("MAX commitment reproduction".into()); } Ok(())
    }
    fn cap_controls(binding: &MaxBinding, declaration: &Declaration, bytes: &[u8], base: &Transcript,
        claim: &InputClaim) -> Result<(), String> {
        let fixed = FixedX::from_authenticated_bits(&declaration.block)?;
        let mut wrong = claim.clone(); wrong.point.pop();
        assert_eq!(fixed.authenticate(&wrong).unwrap_err(), "MAX cap terminal dimension");
        wrong = claim.clone(); wrong.value += Fr::one();
        assert_eq!(fixed.authenticate(&wrong).unwrap_err(), "MAX cap terminal known-X");
        let wire = (0usize..2048usize).find(|w| !cap::eq_at(&claim.point, *w).is_zero()).unwrap();
        let weight = cap::eq_at(&claim.point, wire); assert!(!weight.is_zero());
        let mut changed = FixedX { values: fixed.values.clone() }; let previous = changed.values[wire];
        changed.values[wire] = Fr::one() - previous;
        assert_eq!(gkr::mle(&changed.values, &claim.point).map_err(|e| e.to_string())? - claim.value,
            (Fr::one() - previous - previous) * weight);
        assert_eq!(changed.authenticate(claim).unwrap_err(), "MAX cap terminal known-X");
        let stmt = declaration.statement()?; let circuit = cap::materialize(&stmt);
        let proof = sparse::decode_proof(&circuit, 0, bytes)?;
        for axis in 0usize..4usize {
            let mut fault = proof.clone(); let expected = match axis {
                0 => { fault.layers[0].rounds[0][0] += Fr::one(); GkrError::SumcheckIdentity },
                1 => { fault.layers[0].line_coefficients[0] += Fr::one(); GkrError::LineEndpoints },
                2 => { fault.layers[0].rounds.pop(); GkrError::SumcheckRoundCount },
                _ => { fault.layers[0].line_coefficients.pop(); GkrError::LineDegree },
            };
            let mut t = base.clone();
            let failure = gkr::verify_with_wiring(&[11], 4096, &fault, &mut t,
                |t| binding.cap_bind(declaration, t), |_, r, u, v| cap::coefficients(&stmt, r, u, v));
            assert_eq!(failure, Err(expected));
        }
        let mut short = bytes.to_vec(); short.pop(); assert!(verify_cap(binding, declaration, &short, base).is_err());
        let mut trailing = bytes.to_vec(); trailing.push(0); assert!(verify_cap(binding, declaration, &trailing, base).is_err());
        let mut q_fault = declaration.clone(); q_fault.q += 1u8;
        let q_circuit = cap::materialize(&q_fault.statement()?);
        assert!(cap::group("q-anchors").any(|row| !cap::residuals(&q_circuit, &fixed.values)[row].is_zero()));
        assert!(verify_cap(binding, &q_fault, bytes, base).is_err());
        Ok(())
    }
    fn foreign_source(original: &[u8]) -> Result<PackedFile, String> {
        let path = std::env::var_os("NIPOPOW_MAX_CAP_FOREIGN_WITNESS").map(PathBuf::from)
            .ok_or("missing pinned foreign MAX-cap witness")?;
        let source = PackedFile::open(&path, 22)?;
        let bytes = pinned_bytes(&path, 524288, FOREIGN_DIGEST)?;
        let differences: Vec<usize> = original.iter().zip(&bytes).enumerate()
            .filter_map(|(i, (a, b))| (a != b).then_some(i)).collect();
        if differences != [124928usize] || original[124928] ^ bytes[124928] != 1u8 {
            return Err("foreign witness exact one-bit difference".into());
        }
        Ok(source)
    }
    fn run_same_commitment() -> Result<(), String> {
        let f = fixture()?; let key = verifier_key::admit(22, KEY)?;
        let verified = VerifiedMax::admit(&f.public, &f.artifact, &key)?;
        let binding = &verified.binding; let declaration = Declaration::new(f.block, f.q.clone())?;
        // Repeat the deciding bounded reference gate before any setup/commit/open operation.
        pure_controls(&f, binding, &declaration)?;
        let foreign_reader = foreign_source(&f.bytes)?;
        let foreign_block = read_block(&foreign_reader, DESC)?;
        assert_eq!(&foreign_block[1..], &f.block[1..]); assert_ne!(foreign_block[0], f.block[0]);
        let foreign_m = number(&foreign_block[..224]); assert_eq!(foreign_m, BigUint::from(1199990374401u64));
        let foreign_q = reference(&foreign_m)?.q; assert_eq!(foreign_q, f.q);
        let foreign_declaration = Declaration::new(foreign_block, foreign_q)?;
        let setup = pcs::generate_setup(22)?;
        let verifier_bytes = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))?;
        recovery_guard(&setup, &key, &verifier_bytes)?;
        let mut wrong_setup = setup.clone(); wrong_setup.id[0] ^= 1;
        assert_eq!(recovery_guard(&wrong_setup, &key, &verifier_bytes).unwrap_err(), "MAX setup reproduction"); drop(wrong_setup);
        let mut wrong_key_bytes = verifier_bytes.clone(); wrong_key_bytes[0] ^= 1;
        assert_eq!(recovery_guard(&setup, &key, &wrong_key_bytes).unwrap_err(), "MAX verifier bytes reproduction");
        let committed = packed::commit(&f.source, &setup)?;
        assert_eq!((committed.nu, committed.sigma, committed.rows.len()), (11, 11, 2048));
        let encoded_commitment = pcs::encode_commitment(&committed.commitment)?;
        commitment_guard(&encoded_commitment, &f.artifact.commitment)?;
        let mut wrong_commitment = encoded_commitment.clone(); wrong_commitment[0] ^= 1;
        assert_eq!(commitment_guard(&wrong_commitment, &f.artifact.commitment).unwrap_err(), "MAX commitment reproduction");
        let (mut producer_t, p, value) = projection(binding, &declaration, Fault::None)?;
        assert_eq!(f.source.evaluate(&p)?, value); // Differential only; expected value is declared-block MLE.
        let proof = packed::open(&committed, &f.source, &p, &setup, &mut producer_t)?;
        let opening = pcs::encode_proof(&proof)?;
        let consumer_t = verify_projection(binding, &declaration, &opening, &key, Fault::None)?;
        assert_eq!(producer_t.challenges(), consumer_t.challenges());
        assert_eq!(producer_t.clone().challenge_scalar(b"MAX-projection-continuation"),
            consumer_t.clone().challenge_scalar(b"MAX-projection-continuation"));
        let (cap_bytes, producer_claim, cap_t) = prove_cap(binding, &declaration, &producer_t)?;
        let (claim, verifier_t) = verified.consume(&declaration, &opening, &cap_bytes, &key)?;
        assert_eq!(claim, producer_claim); assert_eq!(cap_t.challenges(), consumer_t.challenges() + 35);
        assert_eq!(verifier_t.challenges(), cap_t.challenges());
        assert_eq!(cap_t.clone().challenge_scalar(b"MAX-cap-continuation"),
            verifier_t.clone().challenge_scalar(b"MAX-cap-continuation"));
        cap_controls(binding, &declaration, &cap_bytes, &consumer_t, &claim)?;
        for fault in FS_FAULTS {
            assert!(verify_projection(binding, &declaration, &opening, &key, fault).is_err(), "actual consumer {fault:?}");
        }
        for bit in [0usize, 224usize] {
            let mut altered = declaration.clone(); altered.block[bit] = !altered.block[bit];
            assert!(verify_projection(binding, &altered, &opening, &key, Fault::None).is_err(), "declared bit {bit}");
        }
        let mut changed_q = declaration.clone(); changed_q.q += 1u8;
        assert!(verify_projection(binding, &changed_q, &opening, &key, Fault::None).is_err());
        let mut short = opening.clone(); short.pop(); assert!(verify_projection(binding, &declaration, &short, &key, Fault::None).is_err());
        let mut trailing = opening.clone(); trailing.push(0); assert!(verify_projection(binding, &declaration, &trailing, &key, Fault::None).is_err());
        // Genuine X2 opening and valid local q(M2), with no claim of a second native/MAX packet.
        let foreign_committed = packed::commit(&foreign_reader, &setup)?;
        let foreign_commitment = pcs::encode_commitment(&foreign_committed.commitment)?;
        assert_ne!(foreign_commitment, f.artifact.commitment);
        let foreign_binding = MaxBinding::new(&f.public, &key, &foreign_commitment)?;
        let (mut foreign_pt, foreign_p, foreign_value) = projection(&foreign_binding, &foreign_declaration, Fault::None)?;
        assert_eq!(foreign_reader.evaluate(&foreign_p)?, foreign_value);
        let foreign_proof = packed::open(&foreign_committed, &foreign_reader, &foreign_p, &setup, &mut foreign_pt)?;
        let foreign_opening = pcs::encode_proof(&foreign_proof)?;
        let foreign_vt = verify_projection(&foreign_binding, &foreign_declaration, &foreign_opening, &key, Fault::None)?;
        assert_eq!(foreign_pt.challenges(), foreign_vt.challenges());
        assert_eq!(foreign_pt.clone().challenge_scalar(b"MAX-projection-continuation"),
            foreign_vt.clone().challenge_scalar(b"MAX-projection-continuation"));
        let (foreign_cap, foreign_claim, foreign_cap_t) = prove_cap(&foreign_binding, &foreign_declaration, &foreign_pt)?;
        let (positive_claim, foreign_end) = verify_cap(&foreign_binding, &foreign_declaration, &foreign_cap, &foreign_vt)?;
        assert_eq!(positive_claim, foreign_claim); assert_eq!(foreign_cap_t.challenges(), foreign_end.challenges());
        assert_eq!(foreign_cap_t.clone().challenge_scalar(b"MAX-cap-continuation"),
            foreign_end.clone().challenge_scalar(b"MAX-cap-continuation"));
        assert!(verify_projection(binding, &foreign_declaration, &foreign_opening, &key, Fault::None).is_err());
        assert!(verified.consume(&foreign_declaration, &foreign_opening, &foreign_cap, &key).is_err());
        // Fixture custody after every operation; no test writes or proof exports.
        let after = baseline_packet(&baseline_directory()?, &f.public)?;
        assert_eq!(after.commitment, f.artifact.commitment); assert_eq!(after.batch, f.artifact.batch);
        for role in 0usize..7usize { assert_eq!(after.roles[role].bytes, f.artifact.roles[role].bytes); }
        check_native_bundle()?; drop(foreign_source(&f.bytes)?);
        Ok(())
    }
    #[test]
    #[ignore = "requires pinned MAX/native/foreign inputs and bounded PCS recovery runner"]
    fn same_commitment_projection_and_cap() { run_same_commitment().unwrap(); }
}
