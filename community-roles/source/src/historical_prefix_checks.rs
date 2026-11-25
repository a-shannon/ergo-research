//! Test-only residual join for shared, real N3/N4 Mainnet prefix witnesses.
//!
//! These checks establish local producer compatibility for this prefix only;
//! they do not build a proof or authenticate a historical chain.

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use ark_bn254::Fr;
    use ark_ff::{One, Zero};
    use blake2::{digest::consts::U32, Blake2b, Digest};

    use crate::{
        daa_work_actions::DaaWorkActions,
        gkr::Gate,
        header_adjacency_layout::HeaderAdjacencyLayout,
        header_height_layout::HeaderHeightLayout,
        header_metadata_order_layout::HeaderMetadataOrderLayout,
        historical_prefix_witness::{self as prefix, Fault, PrefixWitness},
        point_membership, segment_points,
        sparse::Term,
        work_tree_fixed_hash as fixed,
        work_tree_history_plan::WorkTreeHistoryPlan,
        work_tree_layout::{self as layout, Endpoints, WIDTH},
        work_tree_leaf_hash as leaf,
        work_tree_wiring::{Family, Topology},
        work_tree_work as work,
    };

    const N: usize = 3;
    const S: usize = 4;
    const INPUT_LEN: usize = S * WIDTH;
    const HEADER_ROW_WIDTH: usize = 1 << 19;
    const CORE_ROW_WIDTH: usize = 1 << 17;
    const ADJACENCY_LOCAL_ROW_WIDTH: usize = 1 << 9;
    const ID_BITS: usize = 256;
    const METADATA_ORDER_ROW_WIDTH: usize = 1 << 12;
    const HEIGHT_ROW_WIDTH: usize = 32;
    const POINT_ROW_WIDTH: usize = 1 << 14;
    const POINT_INPUT_OFFSET: usize = segment_points::POINT_OFFSET;
    const HEADER_FULL_TERMS: usize = 474_755;
    const HEADER_RETIRED_TERMS: usize = 78_194;
    const HEADER_A4_OMITTED: usize = 0;
    const PREFIX_FIXTURE_BYTES: usize = 1_296_886;
    const PREFIX_FIXTURE_BLAKE2B256: &str =
        "a7f16f32877e49fe94a5f34e3b3231a5de28d2ca2b97f39c5ada6346739e500f";
    const HEADER_RETAINED_EMITTED: usize =
        HEADER_FULL_TERMS - HEADER_RETIRED_TERMS - HEADER_A4_OMITTED;

    fn fixture() -> Result<(Vec<ergo_header_core::Header>, PrefixWitness), String> {
        let headers = prefix::retained_headers()?;
        let witness = prefix::build(&headers)?;
        Ok((headers, witness))
    }

    fn plan_for(witness: &PrefixWitness) -> Result<WorkTreeHistoryPlan, String> {
        let n = witness.raw.len();
        if !(3..=4).contains(&n) {
            return Err("prefix plan requires N3 or N4".into());
        }
        WorkTreeHistoryPlan::compile(n as u64, 2, witness.root, witness.total)
    }

    fn collect_terms(
        family: &str,
        owner: usize,
        input: &[Fr],
        row_base: usize,
        row_count: usize,
        expected_count: usize,
        terms: impl IntoIterator<Item = Term>,
    ) -> Result<Vec<usize>, String> {
        if input.len() != INPUT_LEN || row_count == 0 || row_count > HEADER_ROW_WIDTH {
            return Err(format!(
                "{family}/owner{owner}: checker dimensions rejected"
            ));
        }
        let mut rows = vec![Fr::zero(); row_count];
        let mut count = 0usize;
        for term in terms {
            let row = term
                .row
                .checked_sub(row_base)
                .filter(|row| *row < row_count)
                .ok_or_else(|| format!("{family}/owner{owner}: emitted row outside family"))?;
            if term.gate.left >= input.len() || term.gate.right >= input.len() {
                return Err(format!(
                    "{family}/owner{owner}: emitted wire outside witness"
                ));
            }
            rows[row] += term.gate.evaluate(input);
            count = count
                .checked_add(1)
                .ok_or_else(|| format!("{family}/owner{owner}: term count overflow"))?;
        }
        if count != expected_count {
            return Err(format!(
                "{family}/owner{owner}: term count {count}, expected {expected_count}"
            ));
        }
        Ok(rows
            .iter()
            .enumerate()
            .filter_map(|(row, value)| (!value.is_zero()).then_some(row + row_base))
            .collect())
    }

    #[derive(Debug, PartialEq, Eq)]
    struct Failure {
        family: String,
        owner: usize,
        rows: Vec<usize>,
    }
    impl Failure {
        fn new(family: &str, owner: usize, rows: Vec<usize>) -> Self {
            Self {
                family: family.into(),
                owner,
                rows,
            }
        }
    }
    fn record_rows(report: &mut Vec<Failure>, family: &str, owner: usize, rows: Vec<usize>) {
        if !rows.is_empty() {
            report.push(Failure::new(family, owner, rows));
        }
    }
    fn require_rows(
        report: &mut Vec<Failure>,
        family: &str,
        owner: usize,
        input: &[Fr],
        row_base: usize,
        row_count: usize,
        expected_count: usize,
        terms: impl IntoIterator<Item = Term>,
    ) -> Result<(), String> {
        let failed = collect_terms(
            family,
            owner,
            input,
            row_base,
            row_count,
            expected_count,
            terms,
        )?;
        record_rows(report, family, owner, failed);
        Ok(())
    }

    fn topology_terms(topology: &Topology, family_name: &str) -> Result<(Family, usize), String> {
        let family = topology
            .families
            .iter()
            .find(|family| family.name == family_name)
            .cloned()
            .ok_or_else(|| format!("missing topology family {family_name}"))?;
        let count = family.count(&topology.descriptor)?.terms as usize;
        Ok((family, count))
    }

    fn check_topology_family(
        plan: &WorkTreeHistoryPlan,
        witness: &PrefixWitness,
        family_name: &str,
    ) -> Result<Vec<usize>, String> {
        let topology = plan.topology();
        let (family, expected) = topology_terms(topology, family_name)?;
        let count = family.count(&topology.descriptor)?;
        let row_count = 1usize
            .checked_shl(count.row_log as u32)
            .ok_or_else(|| format!("{family_name}: row domain overflow"))?;
        if row_count > HEADER_ROW_WIDTH {
            return Err(format!("{family_name}: exceeds bounded row scratch"));
        }
        let mut terms = Vec::with_capacity(expected);
        family.emit_terms(&topology.descriptor, |term| {
            terms.push(term);
            Ok(())
        })?;
        collect_terms(
            family_name,
            usize::MAX,
            &witness.values,
            0,
            row_count,
            expected,
            terms,
        )
    }

    fn check_work_link(
        plan: &WorkTreeHistoryPlan,
        witness: &PrefixWitness,
        family_name: &str,
    ) -> Result<Vec<usize>, String> {
        let boundary = plan.work_boundary();
        let family = boundary
            .links()
            .iter()
            .find(|family| family.name == family_name)
            .ok_or_else(|| format!("missing work link {family_name}"))?;
        let count = family.count(plan.descriptor())?;
        let row_count = 1usize
            .checked_shl(count.row_log as u32)
            .ok_or_else(|| format!("{family_name}: row domain overflow"))?;
        if row_count > HEADER_ROW_WIDTH {
            return Err(format!("{family_name}: exceeds bounded row scratch"));
        }
        let mut terms = Vec::with_capacity(count.terms as usize);
        family.emit_terms(plan.descriptor(), |term| {
            terms.push(term);
            Ok(())
        })?;
        collect_terms(
            family_name,
            usize::MAX,
            &witness.values,
            0,
            row_count,
            count.terms as usize,
            terms,
        )
    }

    fn check_numeric_owner(
        plan: &WorkTreeHistoryPlan,
        witness: &PrefixWitness,
        owner: usize,
        expected: usize,
    ) -> Result<Vec<usize>, String> {
        let action = DaaWorkActions::new(plan)?;
        let mut terms = Vec::with_capacity(expected);
        let emitted = action.visit_owner(owner, |term| {
            terms.push(term);
            Ok(())
        })?;
        if emitted != expected {
            return Err(format!(
                "numeric owner {owner}: emitted {emitted}, expected {expected}"
            ));
        }
        collect_terms(
            "numeric_daa_work_actions",
            owner,
            &witness.values,
            0,
            1 << action.row_log(),
            expected,
            terms,
        )
    }

    fn check_adjacency(
        layout: &HeaderAdjacencyLayout,
        witness: &PrefixWitness,
        owner: usize,
        expected: usize,
    ) -> Result<Vec<usize>, String> {
        if layout.input_len() != INPUT_LEN
            || layout.row_log() < layout.slot_log()
            || (1usize << layout.row_log()) != layout.row_count()
        {
            return Err("adjacency dimensions differ from the four-slot witness".into());
        }
        let local_rows = 1usize << (layout.row_log() - layout.slot_log());
        if local_rows != ADJACENCY_LOCAL_ROW_WIDTH {
            return Err("adjacency local row geometry changed".into());
        }
        let row_base = owner * local_rows;
        let mut terms = Vec::with_capacity(expected);
        let emitted = layout.visit_slot_terms(owner as u64, |row, gate| {
            terms.push(Term { row, gate });
            Ok(())
        })?;
        if emitted != expected {
            return Err(format!(
                "adjacency owner {owner}: emitted {emitted}, expected {expected}"
            ));
        }
        collect_terms(
            "header_id_adjacency",
            owner,
            &witness.values,
            row_base,
            local_rows,
            expected,
            terms,
        )
    }

    fn check_core_bank(
        engine: &fixed::Engine,
        witness: &PrefixWitness,
        owner: usize,
        bank: usize,
    ) -> Result<Vec<usize>, String> {
        let offset = *layout::CORE_OFFSETS
            .get(bank)
            .ok_or("core bank outside immutable layout")?;
        let input_base = owner * WIDTH + offset;
        let row_base = bank * CORE_ROW_WIDTH;
        let mut rows = vec![Fr::zero(); CORE_ROW_WIDTH];
        for term in &engine.core.terms {
            let row = term
                .row
                .checked_sub(0)
                .filter(|row| *row < CORE_ROW_WIDTH)
                .ok_or("core compression row outside local bank")?;
            let gate = Gate {
                left: input_base + term.gate.left,
                right: input_base + term.gate.right,
                c0: term.gate.c0,
                c1: term.gate.c1,
                c2: term.gate.c2,
                c3: term.gate.c3,
            };
            if gate.left >= witness.values.len() || gate.right >= witness.values.len() {
                return Err("core compression endpoint outside shared witness".into());
            }
            rows[row] += gate.evaluate(&witness.values);
        }
        let failed = rows
            .iter()
            .enumerate()
            .filter_map(|(row, value)| (!value.is_zero()).then_some(row + row_base))
            .collect::<Vec<_>>();
        Ok(failed)
    }

    fn all_failures(witness: &PrefixWitness) -> Result<Vec<Failure>, String> {
        let n = witness.raw.len();
        if !(3..=4).contains(&n) {
            return Err("prefix checker requires N3 or N4".into());
        }
        let mut report = Vec::new();
        let source = include_bytes!(
            "../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json"
        );
        let source_hash = Blake2b::<U32>::digest(source)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        if source.len() != PREFIX_FIXTURE_BYTES || source_hash != PREFIX_FIXTURE_BLAKE2B256 {
            return Err("retained Mainnet prefix source identity changed".into());
        }
        if witness.values.len() != INPUT_LEN {
            return Err("N3/N4 common witness must have exactly four physical slots".into());
        }
        if witness
            .values
            .iter()
            .any(|value| *value != Fr::zero() && *value != Fr::one())
        {
            return Err("N3/N4 common witness contains a non-Boolean field".into());
        }
        let plan = plan_for(witness)?;
        if plan.headers() != n as u64 || plan.slot_log() != 2 || plan.slots() != S {
            return Err("N3/N4 plan dimensions changed".into());
        }
        let mask = plan.assignment_replacement_mask()?;
        if mask.len() != WIDTH {
            return Err("N3/N4 producer replacement mask width changed".into());
        }
        let mut expected_mask = vec![false; WIDTH];
        for range in [
            327_680..524_288,
            720_896..786_432,
            851_968..983_040,
            655_628..655_654,
            983_040..989_658,
            989_730..991_232,
        ] {
            expected_mask[range].fill(true);
        }
        if expected_mask.iter().filter(|bit| **bit).count() != 401_362
            || mask != expected_mask
            || mask[989_658..989_730].iter().any(|bit| *bit)
            || mask[991_232..999_424].iter().any(|bit| *bit)
        {
            return Err("N3/N4 assignment replacement mask or protected ranges changed".into());
        }

        // Every code-owned core bank is evaluated separately for every owner.
        let engine = fixed::engine()?;
        let core = crate::core_pool::Plan::new(2)?;
        if layout::CORE_OFFSETS.len() != 11 || core.term_count() != engine.core.terms.len() * 11 * S
        {
            return Err("eleven-bank/four-owner compression roster changed".into());
        }
        let mut identities = BTreeSet::<String>::new();
        for owner in 0..S {
            for bank in 0..11 {
                if !identities.insert(format!("compression-core/{owner}/{bank}")) {
                    return Err("duplicate compression bank identity".into());
                }
                let failed = check_core_bank(&engine, witness, owner, bank)?;
                record_rows(
                    &mut report,
                    &format!("compression-core/bank{bank}"),
                    owner,
                    failed,
                );
            }
        }

        // Retained complete header boundary: one independent family namespace
        // per physical owner, with retirement and A4 counts checked explicitly.
        for owner in 0..S {
            let mut terms = Vec::with_capacity(HEADER_RETAINED_EMITTED);
            let counts = plan.visit_slot_terms(owner as u64, |term| {
                terms.push(term);
                Ok(())
            })?;
            if counts.emitted != HEADER_RETAINED_EMITTED
                || counts.omitted_worktree != HEADER_RETIRED_TERMS
                || counts.omitted_a4 != HEADER_A4_OMITTED
            {
                return Err(format!(
                    "retained-header/owner{owner}: count or retirement changed"
                ));
            }
            if !identities.insert(format!("retained-full-header/{owner}")) {
                return Err("duplicate retained-header identity".into());
            }
            require_rows(
                &mut report,
                "retained-full-header",
                owner,
                &witness.values,
                owner * HEADER_ROW_WIDTH,
                HEADER_ROW_WIDTH,
                HEADER_RETAINED_EMITTED,
                terms,
            )?;
        }

        // Fixed node/profile and B3 leaf hash locals, including real dummy
        // compressor assignments rather than zero-filled traces.
        let fixed_profile = plan.fixed_profile();
        let fixed_counts = fixed::count(&engine, fixed_profile)?;
        let mut fixed_total = 0usize;
        for owner in 0..S {
            let mut terms = Vec::new();
            fixed::emit_slot(&engine, fixed_profile, owner, |term| terms.push(term))?;
            let count = terms.len();
            fixed_total += count;
            require_rows(
                &mut report,
                "fixed-node-profile-local",
                owner,
                &witness.values,
                owner * fixed::ROW_WIDTH,
                fixed::ROW_WIDTH,
                count,
                terms,
            )?;
        }
        if fixed_total != fixed_counts.total_boundary_terms as usize {
            return Err("fixed node/profile total differs from code-owned count".into());
        }

        let leaf_boundary = plan.leaf_boundary();
        let leaf_report = leaf::count(&engine, leaf_boundary)?;
        let expected_leaf_total = leaf_report["new_boundary_terms"]
            .as_u64()
            .ok_or("leaf term count missing")? as usize;
        let mut leaf_total = 0usize;
        for owner in 0..S {
            let mut terms = Vec::new();
            leaf_boundary.emit_slot(owner, |term| terms.push(term))?;
            let count = terms.len();
            leaf_total += count;
            require_rows(
                &mut report,
                "leaf-hash-local",
                owner,
                &witness.values,
                owner * leaf::ROW_WIDTH,
                leaf::ROW_WIDTH,
                count,
                terms,
            )?;
        }
        if leaf_total != expected_leaf_total {
            return Err("leaf local total differs from code-owned count".into());
        }

        // Native U224 local arithmetic is checked at each role, with the
        // padding arithmetic family present only for its declared roles.
        let work_boundary = plan.work_boundary();
        let work_groups = work_boundary.groups();
        let mut work_total = 0usize;
        let mut work_expected_total = 0usize;
        for owner in 0..S {
            let expected = work_groups
                .iter()
                .filter(|group| {
                    if group.name == "padding_arithmetic_zero" {
                        owner >= n - 1 && owner < plan.descriptor().leaves
                    } else {
                        owner < n - 1
                    }
                })
                .map(|group| group.term_count)
                .sum::<usize>();
            work_expected_total += expected;
            let mut terms = Vec::with_capacity(expected);
            work_boundary.emit_slot(owner, |term| terms.push(term))?;
            work_total += terms.len();
            require_rows(
                &mut report,
                "native-u224-work-local",
                owner,
                &witness.values,
                owner * work::LOCAL_ROW_WIDTH,
                work::LOCAL_ROW_WIDTH,
                expected,
                terms,
            )?;
        }
        if work_total != work_expected_total {
            return Err("native work local terms differ from role-specific group counts".into());
        }

        // Each topology family retains its own code-owned name and row space.
        let topology = plan.topology();
        topology.validate()?;
        let mut topology_names = BTreeSet::new();
        let mut topology_total = 0usize;
        for family in &topology.families {
            if !topology_names.insert(family.name.clone()) {
                return Err(format!("duplicate topology family {}", family.name));
            }
            let count = family.count(&topology.descriptor)?;
            let row_count = 1usize
                .checked_shl(count.row_log as u32)
                .ok_or("topology family row domain overflow")?;
            if row_count > HEADER_ROW_WIDTH {
                return Err(format!("topology {} exceeds row scratch", family.name));
            }
            let mut terms = Vec::with_capacity(count.terms as usize);
            family.emit_terms(&topology.descriptor, |term| {
                terms.push(term);
                Ok(())
            })?;
            topology_total += terms.len();
            require_rows(
                &mut report,
                &format!("topology/{}", family.name),
                usize::MAX,
                &witness.values,
                0,
                row_count,
                count.terms as usize,
                terms,
            )?;
        }
        if topology_names.is_empty() || topology_total == 0 {
            return Err("topology roster unexpectedly empty".into());
        }

        // Work continuity and public-total links are distinct from local U224
        // arithmetic and from topology families.
        let work_link_count = work_boundary.links().len();
        if work_link_count != 3 {
            return Err("work first/continuity/public-total link roster changed".into());
        }
        for link in work_boundary.links() {
            if !identities.insert(format!("work-link/{}", link.name)) {
                return Err(format!("duplicate work link {}", link.name));
            }
            let failed = check_work_link(&plan, witness, &link.name)?;
            record_rows(
                &mut report,
                &format!("work-link/{}", link.name),
                usize::MAX,
                failed,
            );
        }

        // HeaderID and signed height/time metadata use independent canonical
        // layouts over the same four-slot Boolean input.
        let id_layout = HeaderAdjacencyLayout::compile(n as u64, 2, [0; 32], witness.tip)?;
        let metadata_order = HeaderMetadataOrderLayout::compile(n as u64, 2, witness.tip_time)?;
        let height = HeaderHeightLayout::compile(n as u64, 2)?;
        let expected_adjacency_total = id_layout.term_count();
        let expected_metadata_total = metadata_order.term_count();
        if expected_adjacency_total != (n + 1) * ID_BITS
            || expected_metadata_total != n * (2081 + ID_BITS) + ID_BITS
            || height.fingerprint().is_empty()
        {
            return Err("header ID/metadata adjacency term roster changed".into());
        }
        for (relation_name, relation) in [("header-id", &id_layout)] {
            for owner in 0..n {
                let expected = ID_BITS * if owner + 1 == n { 2 } else { 1 };
                let failed = check_adjacency(relation, witness, owner, expected)?;
                record_rows(&mut report, relation_name, owner, failed);
            }
        }

        // Previous/current timestamp and metadata order must use the full
        // composite consumer, including all 2,081 fixed local-order gates.
        for owner in 0..n {
            let expected = 2081 + ID_BITS * if owner + 1 == n { 2 } else { 1 };
            let mut terms = Vec::with_capacity(expected);
            let emitted = metadata_order.visit_slot_terms(owner as u64, |row, gate| {
                terms.push(Term { row, gate });
                Ok(())
            })?;
            if emitted != expected {
                return Err(format!(
                    "metadata/order owner {owner}: emitted {emitted}, expected {expected}"
                ));
            }
            let failed = collect_terms(
                "header-metadata-order-composite",
                owner,
                &witness.values,
                owner * METADATA_ORDER_ROW_WIDTH,
                METADATA_ORDER_ROW_WIDTH,
                expected,
                terms,
            )?;
            record_rows(&mut report, "header-metadata-order", owner, failed);
        }

        // Serialized height == active slot + 1, evaluated per active owner.
        let mut height_total = 0usize;
        for owner in 0..n {
            let mut terms = Vec::with_capacity(HEIGHT_ROW_WIDTH);
            let emitted = height.visit_slot_terms(owner as u64, |term| {
                terms.push(term);
                Ok(())
            })?;
            height_total += emitted;
            let failed = collect_terms(
                "serialized-height",
                owner,
                &witness.values,
                owner * HEIGHT_ROW_WIDTH,
                HEIGHT_ROW_WIDTH,
                HEIGHT_ROW_WIDTH,
                terms,
            )?;
            record_rows(&mut report, "serialized-height", owner, failed);
        }
        if height_total != n * HEIGHT_ROW_WIDTH {
            return Err("serialized-height term count changed".into());
        }

        // The independent secp256k1 membership circuits consume the same
        // packed owner banks, including the retained A4 slots.
        let points = point_membership::build()?;
        if points.circuit.input_len != point_membership::POINT_WIDTH
            || points.circuit.row_count != POINT_ROW_WIDTH
            || points.circuit.terms.len() != point_membership::TERM_COUNT
        {
            return Err("point-membership circuit shape changed".into());
        }
        for owner in 0..S {
            let base = owner * WIDTH + POINT_INPUT_OFFSET;
            let terms = points.circuit.terms.iter().map(|term| Term {
                row: term.row,
                gate: Gate {
                    left: base + term.gate.left,
                    right: base + term.gate.right,
                    c0: term.gate.c0,
                    c1: term.gate.c1,
                    c2: term.gate.c2,
                    c3: term.gate.c3,
                },
            });
            require_rows(
                &mut report,
                "point-membership",
                owner,
                &witness.values,
                0,
                POINT_ROW_WIDTH,
                point_membership::TERM_COUNT,
                terms,
            )?;
        }

        // Native H2..Hn action rows are emitted at their physical child owner.
        for (owner, expected) in [
            (0, 0),
            (1, 225),
            (2, 448),
            (3, if n == 4 { 448 } else { 0 }),
        ] {
            let failed = check_numeric_owner(&plan, witness, owner, expected)?;
            record_rows(&mut report, "numeric-daa", owner, failed);
        }
        Ok(report)
    }

    fn assert_only(witness: &PrefixWitness, expected: Failure) {
        let actual = all_failures(witness).expect("complete relation inventory failed");
        assert_eq!(
            actual,
            vec![expected],
            "mutant must fail only the declared family/owner/rows"
        );
    }

    // Independent native serialization of the work tree, without descriptor,
    // leaf assignment, fixed-slot assignment or witness-builder helpers.
    fn native_prefix_root(
        headers: &[ergo_header_core::Header],
        wrong_padding: bool,
    ) -> ([u8; 32], [u8; 28]) {
        use num_bigint::BigUint;
        fn be28(n: &BigUint) -> [u8; 28] {
            let bytes = n.to_bytes_be();
            assert!(bytes.len() <= 28);
            let mut out = [0; 28];
            out[28 - bytes.len()..].copy_from_slice(&bytes);
            out
        }
        let hash = ergo_header_core::blake2b256;
        let mut profile_bytes = b"nipopow-v2/work-profile/v1\0".to_vec();
        profile_bytes.extend(crate::header_order::MAINNET_GENESIS);
        let profile = hash(&profile_bytes);
        let n = headers.len();
        assert!((3..=4).contains(&n));
        let mut lower = BigUint::from(0u64);
        let mut level = Vec::new();
        for header in &headers[1..] {
            let raw = header.encode().unwrap();
            let upper = &lower + work::native_decode(header.n_bits).unwrap();
            let mut bytes = vec![b'L'];
            bytes.extend(profile);
            bytes.extend((n as u32).to_be_bytes());
            bytes.extend(header.height.to_be_bytes());
            bytes.extend(be28(&lower));
            bytes.extend(be28(&upper));
            bytes.extend((raw.len() as u16).to_be_bytes());
            bytes.extend(raw);
            level.push(hash(&bytes));
            lower = upper;
        }
        let leaves = (n - 1).next_power_of_two();
        while level.len() < leaves {
            let position = level.len();
            let mut bytes = vec![b'P'];
            bytes.extend(profile);
            bytes.extend((n as u32).to_be_bytes());
            bytes.extend(
                ((if wrong_padding {
                    position ^ 1
                } else {
                    position
                }) as u32)
                    .to_be_bytes(),
            );
            assert_eq!(bytes.len(), 41);
            level.push(hash(&bytes));
        }
        let mut height = 1u8;
        while level.len() > 1 {
            level = level
                .chunks_exact(2)
                .enumerate()
                .map(|(position, pair)| {
                    let mut bytes = vec![b'N', height];
                    bytes.extend((position as u32).to_be_bytes());
                    bytes.extend(pair[0]);
                    bytes.extend(pair[1]);
                    assert_eq!(bytes.len(), 70);
                    hash(&bytes)
                })
                .collect();
            height += 1;
        }
        (level[0], be28(&lower))
    }

    #[test]
    fn n4_padding_and_four_active_headers_match_native_root_and_every_family() {
        let headers = prefix::retained_headers_n(4).unwrap();
        let witness = prefix::build(&headers).unwrap();
        assert_eq!(witness.raw.len(), 4);
        assert_eq!(
            witness.raw,
            headers
                .iter()
                .map(|h| h.encode().unwrap())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            (witness.root, witness.total),
            native_prefix_root(&headers, false)
        );
        let plan = plan_for(&witness).unwrap();
        assert_eq!(
            (
                plan.descriptor().genuine,
                plan.descriptor().leaves,
                plan.slots()
            ),
            (3, 4, 4)
        );
        assert_eq!(plan.leaf_profile().role(2).unwrap(), leaf::Role::Genuine);
        assert_eq!(plan.leaf_profile().role(3).unwrap(), leaf::Role::Padding);
        assert_eq!(plan.fixed_profile().role(3).unwrap(), fixed::Role::Profile);
        assert!(all_failures(&witness).unwrap().is_empty());
        let mut packed = vec![0u8; INPUT_LEN / 8];
        for (i, value) in witness.values.iter().enumerate() {
            if value.is_one() {
                packed[i / 8] |= 1 << (i % 8);
            }
        }
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        println!(
            "{}",
            serde_json::json!({"scope":"N4 full shared residuals only",
            "root":hex(&witness.root),"total":hex(&witness.total),"tip":hex(&witness.tip),
            "tip_time":witness.tip_time,"input_blake2b256":hex(&Blake2b::<U32>::digest(&packed)),
            "headers":4,"genuine_work_leaves":3,"padding_work_leaves":1,
            "core_instances":44,"point_instances":4})
        );
    }

    #[test]
    fn n4_padding_position_rebuilds_ancestors_and_fails_only_canonical_leaf_position() {
        let headers = prefix::retained_headers_n(4).unwrap();
        let wrong = prefix::build_inner(&headers, Fault::PaddingPosition).unwrap();
        let expected = native_prefix_root(&headers, true);
        assert_eq!((wrong.root, wrong.total), expected);
        assert_ne!(wrong.root, native_prefix_root(&headers, false).0);
        assert_eq!(
            wrong.raw,
            headers
                .iter()
                .map(|h| h.encode().unwrap())
                .collect::<Vec<_>>()
        );
        // Byte40 bit0 in padding_message_0, after64+512 local rows.
        assert_only(
            &wrong,
            Failure::new(
                "leaf-hash-local",
                3,
                vec![3 * leaf::ROW_WIDTH + 64 + 512 + 40 * 8],
            ),
        );
    }

    #[test]
    fn n4_fourth_header_height_parent_and_bounded_admission_fail_closed() {
        let headers = prefix::retained_headers_n(4).unwrap();
        let mut wrong = headers.clone();
        wrong[3].height += 1;
        assert!(prefix::build(&wrong)
            .err()
            .unwrap()
            .contains("canonical height or parent identity"));
        let mut wrong = headers.clone();
        wrong[3].parent_id[0] ^= 1;
        assert!(prefix::build(&wrong)
            .err()
            .unwrap()
            .contains("canonical height or parent identity"));
        assert!(prefix::retained_headers_n(2).is_err());
        assert!(prefix::retained_headers_n(5).is_err());
        assert!(prefix::build(&headers[..2]).is_err());
        let mut too_many = headers.clone();
        too_many.push(headers[3].clone());
        assert!(prefix::build(&too_many).is_err());
        let n3 = prefix::retained_headers().unwrap();
        assert!(prefix::build_inner(&n3, Fault::PaddingPosition).is_err());

        // Isolate each code-owned node preimage guard before hashing.
        let engine = fixed::engine().unwrap();
        let profile = fixed::FixedProfile::new(4, [0; 32]).unwrap();
        let mut node = vec![0u8; 70];
        node[0] = b'N';
        node[1] = 1;
        for index in [0, 1, 5] {
            let mut malformed = node.clone();
            malformed[index] ^= 1;
            assert!(leaf::assign_fixed_slot_for_prefix(engine, &profile, 0, &malformed)
                .err()
                .unwrap()
                .contains("preimage does not match its descriptor role"));
        }
        for length in [0, 69, 71] {
            let mut malformed = node.clone();
            malformed.resize(length, 0);
            assert!(leaf::assign_fixed_slot_for_prefix(engine, &profile, 0, &malformed)
                .err()
                .unwrap()
                .contains("preimage does not match its descriptor role"));
        }
    }

    #[test]
    fn n3_shared_boolean_witness_satisfies_every_required_family() {
        let (_, witness) = fixture().unwrap();
        assert!(all_failures(&witness).unwrap().is_empty());
        let mut packed = vec![0u8; INPUT_LEN / 8];
        for (i, value) in witness.values.iter().enumerate() {
            if value.is_one() {
                packed[i / 8] |= 1 << (i % 8);
            }
        }
        let hex = |bytes: &[u8]| bytes.iter().map(|b| format!("{b:02x}")).collect::<String>();
        assert_eq!(
            hex(&Blake2b::<U32>::digest(&packed)),
            "df9eb3ad54cc623b91d9f37bbd7d544f94d7acb44f05871ecd52b0bbd2df88e3",
            "the frozen N3 packed witness must remain byte-identical"
        );
        println!(
            "{}",
            serde_json::json!({
                "scope":"N3 common Boolean witness residuals only",
                "headers":N,"physical_slots":S,"input_cells":INPUT_LEN,
                "compression_instances":44,"point_membership_instances":4,
                "input_blake2b256":hex(&Blake2b::<U32>::digest(&packed)),
                "root":hex(&witness.root),"total_be28":hex(&witness.total),
                "tip":hex(&witness.tip),"tip_time":witness.tip_time,
                "raw_lengths":witness.raw.iter().map(Vec::len).collect::<Vec<_>>(),
                "raw_header_ids":witness.raw.iter().map(|raw|hex(&ergo_header_core::blake2b256(raw))).collect::<Vec<_>>()
            })
        );
    }

    #[test]
    fn n3_raw_alias_and_interval_gap_fail_their_exact_consumers() {
        let headers = prefix::retained_headers().unwrap();
        {
            let raw_fault = prefix::build_inner(&headers, Fault::ForeignLeafRaw).unwrap();
            let original = headers[1].encode().unwrap();
            let mut changed = headers[1].clone();
            changed.timestamp ^= 1;
            let changed = changed.encode().unwrap();
            assert_eq!(original.len(), changed.len());
            // HeaderSuccessor source owner1, padded 4186-bit alias width8192.
            // Expected raw bits come from independent native byte encodings.
            let rows = original
                .iter()
                .zip(&changed)
                .enumerate()
                .flat_map(|(i, (a, b))| {
                    (0..8).filter_map(move |bit| {
                        (((a ^ b) >> bit) & 1 == 1).then_some(8192 + 8 * i + bit)
                    })
                })
                .collect::<Vec<_>>();
            assert!(!rows.is_empty());
            assert_only(
                &raw_fault,
                Failure::new(
                    "topology/header_to_leaf_raw_length_nbits_height",
                    usize::MAX,
                    rows,
                ),
            );
        }
        {
            let gap_fault = prefix::build_inner(&headers, Fault::IntervalGap).unwrap();
            // Work interval source owner1, width224 padded256; the gap toggles bit0.
            assert_only(
                &gap_fault,
                Failure::new("work-link/work_interval_continuity", usize::MAX, vec![256]),
            );
        }
    }

    #[test]
    fn n3_retained_point_padding_mutant_fails_only_its_declared_point_row() {
        let (_, mut witness) = fixture().unwrap();
        let wire = 2 * WIDTH + POINT_INPUT_OFFSET + point_membership::USED_BITS;
        assert_eq!(witness.values[wire], Fr::zero());
        witness.values[wire] = Fr::one();
        assert_only(&witness, Failure::new("point-membership", 2, vec![10_370]));
    }

    #[test]
    fn n3_native_child_difficulty_mutant_rebuilds_descendants_then_fails_h2_only() {
        let mut headers = prefix::retained_headers().unwrap();
        headers[1].n_bits ^= 1;
        headers[2].n_bits = headers[1].n_bits;
        headers[2].parent_id = ergo_header_core::blake2b256(&headers[1].encode().unwrap());
        let witness = prefix::build(&headers).unwrap();
        assert_only(&witness, Failure::new("numeric-daa", 1, vec![1]));
    }

    #[test]
    fn n3_root_total_tip_and_signed_time_anchors_are_independent() {
        let (_, mut witness) = fixture().unwrap();
        witness.root[0] ^= 1;
        assert_only(
            &witness,
            Failure::new("topology/public_root", usize::MAX, vec![0]),
        );
        witness.root[0] ^= 1;

        witness.total[0] ^= 1;
        // Public total is BE28; byte0 bit0 is numeric bit216, last genuine leaf1.
        assert_only(
            &witness,
            Failure::new("work-link/work_public_total", usize::MAX, vec![256 + 216]),
        );
        witness.total[0] ^= 1;

        witness.tip[0] ^= 1;
        assert_only(&witness, Failure::new("header-id", 2, vec![2 * 512 + 256]));
        witness.tip[0] ^= 1;

        witness.tip_time ^= 1;
        // Composite metadata family bit11; timestamp follows32 height bits.
        assert_only(
            &witness,
            Failure::new("header-metadata-order", 2, vec![2 * 4096 + 2048 + 256 + 32]),
        );
    }

    #[test]
    fn n3_invalid_height_and_parent_identity_reject_before_witness_output() {
        let headers = prefix::retained_headers().unwrap();
        let mut wrong_height = headers.clone();
        wrong_height[2].height += 1;
        let error = prefix::build(&wrong_height)
            .err()
            .expect("invalid height admitted");
        assert!(
            error.contains("canonical height or parent identity"),
            "{error}"
        );
        let mut wrong_parent = headers;
        wrong_parent[2].parent_id[0] ^= 1;
        let error = prefix::build(&wrong_parent)
            .err()
            .expect("invalid parent admitted");
        assert!(
            error.contains("canonical height or parent identity"),
            "{error}"
        );
    }
}
