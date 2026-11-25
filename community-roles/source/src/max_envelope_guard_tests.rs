// TEST-only authenticated N3 origin2 refusal. No forall-origin/AB/production claim.
mod envelope_guard_tests {
    use super::*;

    const NATIVE_REVISION: &[u8] = b"8995ff243b140e7fe716bd3204423dd35690c2e4";
    const DRAFT_SHA256: &[u8] = b"E798C2CAEE2AE15F02536C28C24505725EB21543651F57E5901A368F5C5156A4";
    const WORK_DOMAIN: &[u8] = b"N3-envelope-origin2-work-projection-v1";
    const WORK_ROLE: &[u8] = b"same-X-leaf2-upper224-in-actual1024block";
    const INITIAL: u64 = 0x011765000000;
    const RESET: u64 = 0x6f98d5000000;
    const MATURITY: u64 = 43410;
    const WORK_FOREIGN_BLAKE2B256: &str = "97A070C03401F9F46B41FE029A9180662F9B6F11A6F2D98D63EB0FF7FC91573D";

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum WorkBank { Upper, Lower }
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct WorkDescriptor {
        n: usize, c: usize, slot_log: usize, input_log: usize, height: usize,
        owner: usize, base: usize, width: usize, upper: usize, selected: usize,
        lsb: bool, bank: WorkBank,
    }
    const WORK: WorkDescriptor = WorkDescriptor { n: 3, c: 4, slot_log: 2, input_log: 22,
        height: 2, owner: 0, base: 987136, width: 1024, upper: 314, selected: 224,
        lsb: true, bank: WorkBank::Upper };
    fn validate_work(d: WorkDescriptor) -> Result<(), String> {
        if d != WORK { return Err("code-owned W2 descriptor".into()); }
        if std::mem::size_of::<usize>() != 8 || d.height.checked_sub(2) != Some(d.owner)
            || d.base % 1024 != 0 || d.upper + d.selected > d.width
            || d.base + d.width > 1usize << 20usize {
            return Err("W2 projection geometry".into());
        }
        Ok(())
    }
    fn before_work<T>(d: WorkDescriptor, f: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
        validate_work(d)?; f()
    }
    fn bind_work(t: &mut Transcript, d: WorkDescriptor) {
        for n in [d.n, d.c, d.slot_log, d.input_log, d.height, d.owner, d.base,
            d.width, d.upper, d.selected, usize::from(d.lsb)] {
            t.append_u64(b"W2-descriptor", n as u64);
        }
        t.append_bytes(b"W2-bank", b"leaf-upper-work");
    }
    fn work_point(d: WorkDescriptor, rho: &[Fr]) -> Result<Vec<Fr>, String> {
        validate_work(d)?;
        if rho.len() != 10 { return Err("W2 rho dimension".into()); }
        let g = d.owner * (1usize << 20usize) + d.base;
        let mut p = rho.to_vec();
        for j in 10usize..22usize { p.push(Fr::from(((g >> j) & 1usize) as u64)); }
        Ok(p)
    }
    #[derive(Clone)]
    struct WorkDeclaration { descriptor: WorkDescriptor, bits: [bool; 1024] }
    impl WorkDeclaration {
        fn read(source: &PackedFile, d: WorkDescriptor) -> Result<Self, String> {
            validate_recipe(RECIPE)?;
            before_work(d, || {
                if source.input_len() != 1usize << 22usize { return Err("W2 source dimension".into()); }
                let g = d.owner * (1usize << 20usize) + d.base;
                let values = source.read_copy(1024, g / 1024)?;
                if values.len() != 1024 || values.iter().any(|x| !x.is_zero() && !x.is_one()) {
                    return Err("W2 block Boolean framing".into());
                }
                Ok(Self { descriptor: d, bits: std::array::from_fn(|i| values[i].is_one()) })
            })
        }
        fn work(&self) -> Result<BigUint, String> {
            validate_work(self.descriptor)?; Ok(number(&self.bits[314..538]))
        }
    }

    #[derive(Clone, Copy)]
    struct Recipe { n: u64, k0: u64, initial: u64, reset: u64, origin: u64, maturity: u64 }
    const RECIPE: Recipe = Recipe { n: 3, k0: 64, initial: INITIAL, reset: RESET, origin: 2, maturity: MATURITY };
    fn validate_recipe(r: Recipe) -> Result<(), String> {
        if r.n != 3 || r.k0 != 64 { return Err("N3 empty introduction roster".into()); }
        if r.initial != INITIAL || r.reset != RESET { return Err("native envelope constants".into()); }
        if r.origin != 2 || r.origin >= 845760 || r.maturity != MATURITY {
            return Err("sampled early-origin2 profile".into());
        }
        Ok(())
    }
    fn grid(n: &BigUint) -> Result<BigUint, String> {
        if n.is_zero() { return Err("positive dyadic input".into()); }
        let mut q = BigUint::from(1u8);
        for _ in 0usize..=64usize {
            if &q >= n { return Ok(q); }
            q <<= 1usize;
        }
        Err("envelope profile coverage".into())
    }
    fn derive_u(q: &BigUint, recipe: Recipe) -> Result<BigUint, String> {
        validate_recipe(recipe)?;
        if &grid(q)? != q { return Err("verified q must be canonical dyadic".into()); }
        let initial = grid(&BigUint::from(recipe.initial))?;
        let reset = grid(&BigUint::from(recipe.reset))?;
        Ok(std::cmp::max(q, &std::cmp::max(initial, reset)).clone())
    }
    fn require_early_cap(cap: &BigUint, derived: &BigUint, recipe: Recipe) -> Result<(), String> {
        validate_recipe(recipe)?;
        if cap != derived { return Err("early V must equal derived U".into()); } Ok(())
    }
    fn query_floor(n: u64, h: u64, k0: u64) -> Result<u64, String> {
        if h < 2 || k0 != 64 { return Err("full-query profile".into()); }
        let required = h.checked_add(k0).ok_or("full-query height overflow")?;
        let f = h.checked_add(k0 - 1).ok_or("full-query floor overflow")?;
        if n >= 1u64 << 31u32 || h >= 1u64 << 31u32 { return Err("full-query height range".into()); }
        if n < required { return Err("N3 full-query immature".into()); } Ok(f)
    }
    fn before_full_query<T>(n: u64, h: u64, k0: u64, f: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
        query_floor(n, h, k0)?; f()
    }
    #[derive(Debug, PartialEq, Eq)]
    enum GuardReject { Underflow, ImmatureOrigin2 }
    // Arithmetic fixtures have no conversion into a native verified receipt or membership token.
    struct ArithmeticCase { total: BigUint, prefix: BigUint, u: BigUint, maturity: u64 }
    impl ArithmeticCase {
        fn check(&self) -> Result<(), GuardReject> {
            if self.total < self.prefix { return Err(GuardReject::Underflow); }
            if &self.total - &self.prefix < &self.u * BigUint::from(self.maturity) {
                return Err(GuardReject::ImmatureOrigin2);
            }
            Ok(())
        }
    }
    // Construction occurs only after complete old MAX verification, MAX PCS and cap verification.
    struct CapReceipt { verified: VerifiedMax, declaration: Declaration,
        cap_end: Transcript, u: BigUint, total: BigUint }
    impl CapReceipt {
        fn earn(f: &Fixture, verified: VerifiedMax, key: &verifier_key::AdmittedVerifierKey,
            setup: &pcs::Setup, committed: &packed::PackedCommitted) -> Result<Self, String> {
            validate_recipe(RECIPE)?;
            let expected = Public::native(3)?;
            if verified.binding.public != expected.bytes()? || key.id() != &verified.binding.key_id {
                return Err("original native MAX context".into());
            }
            recovery_guard(setup, key, &pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))?)?;
            commitment_guard(&pcs::encode_commitment(&committed.commitment)?, &verified.binding.commitment)?;
            let declaration = Declaration::new(f.block, f.q.clone())?;
            let (mut pt, p, value) = projection(&verified.binding, &declaration, Fault::None)?;
            assert_eq!(f.source.evaluate(&p)?, value);
            let opening = pcs::encode_proof(&packed::open(committed, &f.source, &p, setup, &mut pt)?)?;
            let vt = verify_projection(&verified.binding, &declaration, &opening, key, Fault::None)?;
            assert_eq!(pt.challenges(), vt.challenges());
            assert_eq!(pt.clone().challenge_scalar(b"MAX-projection-continuation"), vt.clone().challenge_scalar(b"MAX-projection-continuation"));
            let (cap_bytes, producer_claim, cap_t) = prove_cap(&verified.binding, &declaration, &pt)?;
            let (claim, cap_end) = verified.consume(&declaration, &opening, &cap_bytes, key)?;
            assert_eq!(claim, producer_claim); assert_eq!(cap_t.challenges(), vt.challenges() + 35);
            assert_eq!(cap_t.challenges(), cap_end.challenges());
            assert_eq!(cap_t.clone().challenge_scalar(b"MAX-cap-continuation"), cap_end.clone().challenge_scalar(b"MAX-cap-continuation"));
            let u = derive_u(&declaration.q, RECIPE)?;
            let total = BigUint::from_bytes_be(&expected.total);
            Ok(Self { verified, declaration, cap_end, u, total })
        }
        fn verify_work<'a>(&'a self, declaration: &WorkDeclaration, bytes: &[u8],
            key: &verifier_key::AdmittedVerifierKey) -> Result<AuthenticatedWork<'a>, String> {
            let adapter = WorkAdapter::original(self);
            let transcript = verify_adapter(&adapter, declaration, bytes, key, WorkFault::None)?;
            Ok(AuthenticatedWork { receipt: self, prefix: declaration.work()?, transcript })
        }
    }
    struct AuthenticatedWork<'a> { receipt: &'a CapReceipt, prefix: BigUint, transcript: Transcript }
    impl AuthenticatedWork<'_> {
        fn guard(&self) -> Result<(), GuardReject> {
            ArithmeticCase { total: self.receipt.total.clone(), prefix: self.prefix.clone(),
                u: self.receipt.u.clone(), maturity: MATURITY }.check()
        }
    }
    fn omitted_origin2_consumer(work: &AuthenticatedWork<'_>) -> Result<(), GuardReject> {
        // Counterfactual: the same authenticated inputs pass when the mandatory guard is removed.
        let _ = (&work.receipt.verified, &work.prefix); Ok(())
    }
    #[derive(Clone)]
    struct WorkAdapter { base: Transcript, public: Vec<u8>, corpus: [u8; 32],
        key_id: [u8; 32], commitment: Vec<u8>, q: BigUint, u: BigUint, total: BigUint }
    impl WorkAdapter {
        fn original(receipt: &CapReceipt) -> Self {
            let b = &receipt.verified.binding;
            Self { base: receipt.cap_end.clone(), public: b.public.clone(), corpus: b.corpus,
                key_id: b.key_id, commitment: b.commitment.clone(), q: receipt.declaration.q.clone(),
                u: receipt.u.clone(), total: receipt.total.clone() }
        }
        fn foreign_projection_only(receipt: &CapReceipt, commitment: &[u8]) -> Result<Self, String> {
            pcs::decode_commitment(commitment)?;
            let mut adapter = Self::original(receipt); adapter.commitment = commitment.to_vec(); Ok(adapter)
        }
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum WorkFault { None, MissingBlock, LateBlock, MissingQ, LateQ, MissingU, LateU,
        MissingTotal, LateTotal, MissingMaturity, LateMaturity, Domain, Role, Public,
        Corpus, Key, Commitment, RhoLabel, RhoOrder, ReceiptBase, Reset }
    const WORK_FAULTS: [WorkFault; 20] = [WorkFault::MissingBlock, WorkFault::LateBlock,
        WorkFault::MissingQ, WorkFault::LateQ, WorkFault::MissingU, WorkFault::LateU,
        WorkFault::MissingTotal, WorkFault::LateTotal, WorkFault::MissingMaturity,
        WorkFault::LateMaturity, WorkFault::Domain, WorkFault::Role, WorkFault::Public,
        WorkFault::Corpus, WorkFault::Key, WorkFault::Commitment, WorkFault::RhoLabel,
        WorkFault::RhoOrder, WorkFault::ReceiptBase, WorkFault::Reset];
    fn work_projection(adapter: &WorkAdapter, declaration: &WorkDeclaration, fault: WorkFault)
        -> Result<(Transcript, Vec<Fr>, Fr), String> {
        validate_work(declaration.descriptor)?; validate_recipe(RECIPE)?;
        require_early_cap(&adapter.u, &derive_u(&adapter.q, RECIPE)?, RECIPE)?;
        let mut t = adapter.base.clone(); let start = t.challenges();
        if fault == WorkFault::ReceiptBase { t.append_bytes(b"counterfactual-receipt-base", b"changed"); }
        t.append_bytes(b"W2-domain", if fault == WorkFault::Domain { b"counterfactual-W2-domain" } else { WORK_DOMAIN });
        t.append_bytes(b"W2-role", if fault == WorkFault::Role { b"counterfactual-W2-role" } else { WORK_ROLE });
        t.append_bytes(b"W2-native-revision", NATIVE_REVISION); t.append_bytes(b"W2-draft", DRAFT_SHA256);
        t.append_bytes(b"W2-introduction-rule", b"N3+k64=67<first-legacy-parent1024;empty-roster;include-both-resets");
        t.append_u64(b"W2-initial", INITIAL);
        t.append_u64(b"W2-reset", if fault == WorkFault::Reset { 122702194049536u64 } else { RESET });
        t.append_u64(b"W2-k0", 64); t.append_u64(b"W2-origin", 2);
        let mut public = adapter.public.clone(); let mut corpus = adapter.corpus;
        let mut key = adapter.key_id; let mut commitment = adapter.commitment.clone();
        if fault == WorkFault::Public { public[0] ^= 1; } if fault == WorkFault::Corpus { corpus[0] ^= 1; }
        if fault == WorkFault::Key { key[0] ^= 1; } if fault == WorkFault::Commitment { commitment[0] ^= 1; }
        t.append_bytes(b"W2-public", &public); t.append_bytes(b"W2-corpus", &corpus);
        t.append_bytes(b"W2-key", &key); t.append_bytes(b"W2-commitment", &commitment);
        bind_work(&mut t, declaration.descriptor);
        let block = declaration.bits.map(u8::from);
        let q = adapter.q.to_bytes_le(); let u = adapter.u.to_bytes_le(); let total = adapter.total.to_bytes_le();
        if !matches!(fault, WorkFault::MissingBlock | WorkFault::LateBlock) { t.append_bytes(b"W2-block1024", &block); }
        if !matches!(fault, WorkFault::MissingQ | WorkFault::LateQ) { t.append_bytes(b"W2-verified-q", &q); }
        if !matches!(fault, WorkFault::MissingU | WorkFault::LateU) { t.append_bytes(b"W2-derived-U", &u); }
        if !matches!(fault, WorkFault::MissingTotal | WorkFault::LateTotal) { t.append_bytes(b"W2-public-W3", &total); }
        if !matches!(fault, WorkFault::MissingMaturity | WorkFault::LateMaturity) { t.append_u64(b"W2-sampled-maturity", MATURITY); }
        let mut rho = Vec::with_capacity(10);
        for i in 0usize..10usize {
            let mut label = b"W2-rho-LSB-".to_vec(); label.push(i as u8);
            if fault == WorkFault::RhoLabel && i == 0 { label.push(0); }
            rho.push(t.challenge_scalar(&label));
        }
        if fault == WorkFault::LateBlock { t.append_bytes(b"W2-block1024", &block); }
        if fault == WorkFault::LateQ { t.append_bytes(b"W2-verified-q", &q); }
        if fault == WorkFault::LateU { t.append_bytes(b"W2-derived-U", &u); }
        if fault == WorkFault::LateTotal { t.append_bytes(b"W2-public-W3", &total); }
        if fault == WorkFault::LateMaturity { t.append_u64(b"W2-sampled-maturity", MATURITY); }
        if fault == WorkFault::RhoOrder { rho.reverse(); }
        let p = work_point(declaration.descriptor, &rho)?;
        let value = gkr::mle(&bit_fields(&declaration.bits), &rho).map_err(|e| e.to_string())?;
        assert_eq!(t.challenges(), start + 10); Ok((t, p, value))
    }
    fn verify_adapter(adapter: &WorkAdapter, declaration: &WorkDeclaration, bytes: &[u8],
        key: &verifier_key::AdmittedVerifierKey, fault: WorkFault) -> Result<Transcript, String> {
        if key.log_n() != 22 || key.id() != &adapter.key_id { return Err("W2 original admitted key".into()); }
        let (mut t, p, value) = work_projection(adapter, declaration, fault)?;
        let proof = pcs::decode_proof(bytes, 22)?;
        pcs::verify_admitted(pcs::decode_commitment(&adapter.commitment)?, value, &p, &proof, key, &mut t)?;
        Ok(t)
    }
    fn address_and_arithmetic_controls(f: &Fixture, declaration: &WorkDeclaration) -> Result<(), String> {
        let callbacks = Cell::new(0usize);
        for axis in 0usize..12usize {
            let mut d = WORK; match axis { 0 => d.n += 1, 1 => d.c += 1, 2 => d.slot_log += 1,
                3 => d.input_log += 1, 4 => d.height += 1, 5 => d.owner += 1, 6 => d.base += 1024,
                7 => d.width /= 2, 8 => d.upper += 1, 9 => d.selected -= 1,
                10 => d.lsb = false, _ => d.bank = WorkBank::Lower }
            for _ in 0usize..3usize {
                assert_eq!(before_work(d, || { callbacks.set(callbacks.get() + 1); Ok(()) }).unwrap_err(), "code-owned W2 descriptor");
                assert_eq!(callbacks.get(), 0); // Same-value read/challenge/PCS callbacks all remain untouched.
            }
        }
        for (n, h, k0, reason) in [(3u64, 2u64, 64u64, "N3 full-query immature"),
            (3, 2, 63, "full-query profile"), (3, 1, 64, "full-query profile"),
            (u64::MAX, u64::MAX, 64, "full-query height overflow"),
            (1u64 << 31u32, 2, 64, "full-query height range")] {
            assert_eq!(before_full_query(n, h, k0, || { callbacks.set(callbacks.get() + 1); Ok(()) }).unwrap_err(), reason);
            assert_eq!(callbacks.get(), 0);
        }
        assert_eq!(query_floor(66, 2, 64)?, 65);
        let rho: Vec<Fr> = (2u64..12u64).map(Fr::from).collect(); let p = work_point(WORK, &rho)?;
        assert_eq!(p.len(), 22); assert_eq!(&p[..10], rho.as_slice());
        for j in 10usize..22usize { assert_eq!(p[j], Fr::from(((WORK.base >> j) & 1usize) as u64)); }
        assert_eq!(work_point(WORK, &rho[..9]).unwrap_err(), "W2 rho dimension");
        let expected: [bool; 1024] = std::array::from_fn(|i| (f.bytes[(WORK.base + i) / 8] >> ((WORK.base + i) % 8)) & 1u8 == 1);
        assert_eq!(declaration.bits, expected); assert_eq!(number(&expected[90..314]), BigUint::from(0u8));
        assert_eq!(number(&expected[314..538]), BigUint::from(INITIAL)); assert_eq!(number(&expected[538..762]), BigUint::from(INITIAL));
        let fields = bit_fields(&expected); let baseline = gkr::mle(&fields, &rho).map_err(|e| e.to_string())?;
        for bit in 0usize..1024usize {
            let weight = cap::eq_at(&rho, bit); assert!(!weight.is_zero());
            let mut altered = fields.clone(); let old = altered[bit]; altered[bit] = Fr::one() - old;
            assert_eq!(gkr::mle(&altered, &rho).map_err(|e| e.to_string())? - baseline, (Fr::one() - old - old) * weight);
        }
        for axis in 0usize..6usize {
            let mut recipe = RECIPE; match axis { 0 => recipe.n += 1, 1 => recipe.k0 -= 1,
                2 => recipe.initial += 1, 3 => recipe.reset = 122702194049536,
                4 => recipe.origin = 845760, _ => recipe.maturity = 4995 }
            assert!(validate_recipe(recipe).is_err());
        }
        let q = BigUint::from(1u8) << 41usize; let u = derive_u(&q, RECIPE)?;
        assert_eq!(u, BigUint::from(1u8) << 47usize);
        assert!(require_early_cap(&q, &u, RECIPE).is_err());
        assert!(require_early_cap(&(&u * 2u8), &u, RECIPE).is_err());
        assert!(require_early_cap(&(BigUint::from(1u8) << 65usize), &u, RECIPE).is_err());
        assert!(derive_u(&BigUint::from(0u8), RECIPE).is_err());
        assert!(derive_u(&BigUint::from(3u8), RECIPE).is_err());
        assert!(derive_u(&(BigUint::from(1u8) << 65usize), RECIPE).is_err());
        assert_eq!(grid(&(BigUint::from(1u8) << 64usize))?, BigUint::from(1u8) << 64usize);
        let prefix = BigUint::from(INITIAL); let target = &u * BigUint::from(MATURITY);
        assert_eq!(target, BigUint::from(6109414369504788480u64));
        assert_eq!(BigUint::from_bytes_be(&f.public.total), BigUint::from(2399980748800u64));
        let actual = ArithmeticCase { total: BigUint::from(2399980748800u64), prefix: prefix.clone(), u: u.clone(), maturity: MATURITY };
        assert_eq!(actual.check(), Err(GuardReject::ImmatureOrigin2));
        assert_eq!(&target - (&actual.total - &prefix), BigUint::from(6109413169514414080u64));
        for delta in [-1i8, 0i8, 1i8] {
            let total = if delta < 0 { &prefix + &target - 1u8 } else { &prefix + &target + delta as u8 };
            let case = ArithmeticCase { total, prefix: prefix.clone(), u: u.clone(), maturity: MATURITY };
            assert_eq!(case.check(), if delta < 0 { Err(GuardReject::ImmatureOrigin2) } else { Ok(()) });
        }
        assert_eq!(ArithmeticCase { total: &prefix - 1u8, prefix, u, maturity: MATURITY }.check(), Err(GuardReject::Underflow));
        Ok(())
    }
    #[test]
    fn fixed_envelope_and_work_address() {
        // The full request refuses before the existing fixture loader or any opening.
        assert_eq!(before_full_query(3, 2, 64, || -> Result<(), String> { panic!("immature query reached a read") }).unwrap_err(), "N3 full-query immature");
        let f = fixture().unwrap(); let declaration = WorkDeclaration::read(&f.source, WORK).unwrap();
        address_and_arithmetic_controls(&f, &declaration).unwrap();
    }
    fn guard_foreign(original: &[u8]) -> Result<PackedFile, String> {
        let path = std::env::var_os("NIPOPOW_ENVELOPE_GUARD_FOREIGN_WITNESS").map(PathBuf::from)
            .ok_or("missing pinned W2 foreign witness")?;
        let source = PackedFile::open(&path, 22)?;
        // Root prepares this one-bit fixture before freeze; no test-created source is allowed.
        let bytes = pinned_bytes(&path, 524288, WORK_FOREIGN_BLAKE2B256)?;
        if bytes.len() != original.len() || bytes.len() != 524288 { return Err("W2 foreign framing".into()); }
        let changed: Vec<usize> = original.iter().zip(&bytes).enumerate().filter_map(|(i, (a, b))| (a != b).then_some(i)).collect();
        if changed != [123431usize] || original[123431] ^ bytes[123431] != 4u8 { return Err("W2 foreign exact bit difference".into()); }
        Ok(source)
    }
    fn run_authenticated_origin2() -> Result<(), String> {
        assert_eq!(before_full_query(3, 2, 64, || -> Result<(), String> { panic!("full-profile N3 read") }).unwrap_err(), "N3 full-query immature");
        let f = fixture()?; let declaration = WorkDeclaration::read(&f.source, WORK)?;
        address_and_arithmetic_controls(&f, &declaration)?;
        let key = verifier_key::admit(22, KEY)?;
        let verified = VerifiedMax::admit(&f.public, &f.artifact, &key)?;
        let foreign_source = guard_foreign(&f.bytes)?;
        let foreign_declaration = WorkDeclaration::read(&foreign_source, WORK)?;
        for i in 0usize..1024usize { assert_eq!(foreign_declaration.bits[i] != declaration.bits[i], i == 314); }
        assert_eq!(foreign_declaration.work()?, declaration.work()? + 1u8);
        let setup = pcs::generate_setup(22)?;
        recovery_guard(&setup, &key, &pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))?)?;
        let committed = packed::commit(&f.source, &setup)?;
        commitment_guard(&pcs::encode_commitment(&committed.commitment)?, &f.artifact.commitment)?;
        let receipt = CapReceipt::earn(&f, verified, &key, &setup, &committed)?;
        assert_eq!(receipt.u, BigUint::from(1u8) << 47usize); assert_eq!(receipt.declaration.q, BigUint::from(1u8) << 41usize);
        let adapter = WorkAdapter::original(&receipt);
        let (mut pt, p, value) = work_projection(&adapter, &declaration, WorkFault::None)?;
        assert_eq!(f.source.evaluate(&p)?, value);
        let proof = packed::open(&committed, &f.source, &p, &setup, &mut pt)?;
        let opening = pcs::encode_proof(&proof)?;
        let work = receipt.verify_work(&declaration, &opening, &key)?;
        assert_eq!(pt.challenges(), work.transcript.challenges());
        assert_eq!(pt.clone().challenge_scalar(b"W2-projection-continuation"), work.transcript.clone().challenge_scalar(b"W2-projection-continuation"));
        assert_eq!(work.prefix, BigUint::from(INITIAL)); assert_eq!(work.guard(), Err(GuardReject::ImmatureOrigin2));
        assert_eq!(omitted_origin2_consumer(&work), Ok(()));
        for fault in WORK_FAULTS { assert!(verify_adapter(&adapter, &declaration, &opening, &key, fault).is_err(), "actual W2 consumer {fault:?}"); }
        for bit in [0usize, 16, 26, 58, 90, 313, 314, 537, 538, 761, 762, 1017, 1018, 1023] {
            let mut altered = declaration.clone(); altered.bits[bit] = !altered.bits[bit];
            assert!(receipt.verify_work(&altered, &opening, &key).is_err(), "actual declared bit {bit}");
        }
        let mut short = opening.clone(); short.pop(); assert!(receipt.verify_work(&declaration, &short, &key).is_err());
        let mut trailing = opening.clone(); trailing.push(0); assert!(receipt.verify_work(&declaration, &trailing, &key).is_err());
        // Positive foreign projection only: the one-bit upper mutation violates original MAX work rows.
        let foreign_committed = packed::commit(&foreign_source, &setup)?;
        let foreign_commitment = pcs::encode_commitment(&foreign_committed.commitment)?;
        assert_ne!(foreign_commitment, adapter.commitment);
        let foreign_adapter = WorkAdapter::foreign_projection_only(&receipt, &foreign_commitment)?;
        let (mut foreign_pt, foreign_p, foreign_value) = work_projection(&foreign_adapter, &foreign_declaration, WorkFault::None)?;
        assert_eq!(foreign_source.evaluate(&foreign_p)?, foreign_value);
        let foreign_opening = pcs::encode_proof(&packed::open(&foreign_committed, &foreign_source, &foreign_p, &setup, &mut foreign_pt)?)?;
        let foreign_vt = verify_adapter(&foreign_adapter, &foreign_declaration, &foreign_opening, &key, WorkFault::None)?;
        assert_eq!(foreign_pt.challenges(), foreign_vt.challenges());
        assert_eq!(foreign_pt.clone().challenge_scalar(b"W2-projection-continuation"), foreign_vt.clone().challenge_scalar(b"W2-projection-continuation"));
        assert!(receipt.verify_work(&foreign_declaration, &foreign_opening, &key).is_err());
        let after = baseline_packet(&baseline_directory()?, &f.public)?;
        assert_eq!(after.commitment, f.artifact.commitment); assert_eq!(after.batch, f.artifact.batch);
        for role in 0usize..7usize { assert_eq!(after.roles[role].bytes, f.artifact.roles[role].bytes); }
        check_native_bundle()?; drop(guard_foreign(&f.bytes)?);
        Ok(())
    }
    #[test]
    #[ignore = "requires pinned original MAX/native/W2 foreign input and bounded PCS runner"]
    fn authenticated_origin2_rejection() { run_authenticated_origin2().unwrap(); }
}
