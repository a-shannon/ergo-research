//! Native work, interval sums and header-field copies on one original input.
//! Canonical RAW, the tree root and the remaining DAA families are separate.

use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    daa_work_actions::DaaWorkActions,
    sparse::Term,
    transcript::Transcript,
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::{self as layout, WIDTH},
    work_tree_wiring::{self as wiring, Family, Mapping},
    work_tree_work,
};

const FAMILY_NAMES: [&[u8]; 6] = [
    b"numeric-work-actions",
    b"native-work-local",
    b"work-first-lower-zero",
    b"work-interval-continuity",
    b"work-public-total",
    b"header-to-leaf-raw-length-nbits-height",
];

pub(crate) struct NativeWorkRelation<'a> {
    parent: &'a WorkTreeHistoryPlan,
    actions: DaaWorkActions<'a>,
    links: &'a [Family; 3],
    alias: &'a Family,
    input_log: usize,
    local_row_log: usize,
    row_log: usize,
    source_row_logs: [usize; 6],
    map_fingerprint: String,
    source_hashes: [String; 4],
}

impl<'a> NativeWorkRelation<'a> {
    pub(crate) fn new(parent: &'a WorkTreeHistoryPlan) -> Result<Self, String> {
        let descriptor = parent.descriptor();
        descriptor.validate()?;
        parent.topology().validate()?;
        parent.work_profile().validate()?;
        let h = parent.slot_log();
        if usize::BITS != 64
            || !(2..=21).contains(&h)
            || descriptor.headers as u64 != parent.headers()
            || descriptor.slots != parent.slots()
            || descriptor.slot_log() != h
            || parent.work_boundary().profile() != parent.work_profile()
            || &parent.work_profile().tree != descriptor
            || &parent.topology().descriptor != descriptor
        {
            return Err("native work parent/profile geometry differs".into());
        }

        let actions = DaaWorkActions::new(parent)?;
        let input_log = 20 + h;
        let local_row_log = 13 + h;
        let row_log = local_row_log + 3;
        let source_row_logs = [h, 11 + h, 8 + h, 8 + h, 8 + h, 13 + h];
        if WIDTH != 1 << 20 || actions.input_log() != input_log || actions.row_log() != h
            || 1usize.checked_shl(input_log as u32).is_none()
            || 1usize.checked_shl(row_log as u32).is_none()
        {
            return Err("native work source dimensions differ".into());
        }

        let baseline = layout::shared_baseline()?;
        let e = &baseline.endpoints;
        if e.lower.len() != 224 || e.upper.len() != 224 || e.work.len() != 224
            || e.header_aliases().len() != 4186 || baseline.header_alias_wires.len() != 4186
        {
            return Err("native work endpoint widths differ".into());
        }
        let total_bits = (0..224).map(|bit| {
            (parent.work_profile().total_be28[27 - bit / 8] >> (bit % 8)) & 1
        }).collect();
        let expected_links = [
            Family {
                name: "work_first_lower_zero".into(),
                mapping: Mapping::FixedRight { lo: 0, hi: 1, target: 0 },
                left_wires: e.lower.clone(), right_wires: vec![0; 224],
                constants: Some(vec![0; 224]),
            },
            Family {
                name: "work_interval_continuity".into(),
                mapping: Mapping::HeaderSuccessor { lo: 1, hi: descriptor.genuine },
                left_wires: e.lower.clone(), right_wires: e.upper.clone(), constants: None,
            },
            Family {
                name: "work_public_total".into(),
                mapping: Mapping::FixedRight {
                    lo: descriptor.genuine - 1, hi: descriptor.genuine, target: 0,
                },
                left_wires: e.upper.clone(), right_wires: vec![0; 224],
                constants: Some(total_bits),
            },
        ];
        let links = parent.work_boundary().links();
        if links != &expected_links {
            return Err("native work fixed interval-link identity differs".into());
        }
        let mut matches = parent.topology().families.iter().filter(|family| {
            family.name == "header_to_leaf_raw_length_nbits_height"
        });
        let alias = matches.next().ok_or("native work header alias is missing")?;
        let expected_alias = Family {
            name: "header_to_leaf_raw_length_nbits_height".into(),
            mapping: Mapping::HeaderSuccessor { lo: 1, hi: descriptor.headers },
            left_wires: baseline.header_alias_wires.clone(), right_wires: e.header_aliases(),
            constants: None,
        };
        if matches.next().is_some() || alias != &expected_alias {
            return Err("native work fixed header-alias identity differs".into());
        }
        for (index, family) in links.iter().chain(std::iter::once(alias)).enumerate() {
            let count = family.count(descriptor)?;
            if count.global_input_bits != input_log || count.row_log != source_row_logs[index + 2] {
                return Err("native work family dimensions differ".into());
            }
        }
        let groups = parent.work_boundary().groups();
        let padding = groups.iter().filter(|group| group.name == "padding_arithmetic_zero")
            .map(|group| group.term_count).sum::<usize>();
        let genuine = groups.iter().filter(|group| group.name != "padding_arithmetic_zero")
            .map(|group| group.term_count).sum::<usize>();
        if work_tree_work::LOCAL_ROW_WIDTH != 2048 || genuine != 3265 || padding != 1152 {
            return Err("native work local template census differs".into());
        }
        let map_fingerprint = layout::hash_bytes(&serde_json::to_vec(&(
            parent.work_profile(), groups, links, alias,
        )).map_err(|e| e.to_string())?);
        let source_hashes = [
            layout::hash_bytes(include_bytes!("daa_work_actions.rs")),
            layout::hash_bytes(include_bytes!("work_tree_work.rs")),
            layout::hash_bytes(include_bytes!("work_tree_wiring.rs")),
            layout::hash_bytes(include_bytes!("native_work_relation.rs")),
        ];
        Ok(Self { parent, actions, links, alias, input_log, local_row_log, row_log,
            source_row_logs, map_fingerprint, source_hashes })
    }

    pub(crate) fn input_log(&self) -> usize { self.input_log }
    pub(crate) fn row_log(&self) -> usize { self.row_log }

    pub(crate) fn bind(&self, transcript: &mut Transcript) -> Result<(), String> {
        if transcript.challenges() != 0 {
            return Err("native work relation binding after challenge".into());
        }
        transcript.append_bytes(b"native-work-relation", b"native-work-six-families-v1");
        for value in [6, self.input_log, self.local_row_log, self.row_log] {
            transcript.append_u64(b"native-work-relation-geometry", value as u64);
        }
        transcript.append_bytes(b"native-work-relation-map", self.map_fingerprint.as_bytes());
        for (tag, name) in FAMILY_NAMES.iter().enumerate() {
            transcript.append_u64(b"native-work-family-tag", tag as u64);
            transcript.append_bytes(b"native-work-family-name", name);
            transcript.append_u64(b"native-work-family-row-log", self.source_row_logs[tag] as u64);
        }
        for hash in &self.source_hashes {
            transcript.append_bytes(b"native-work-relation-source", hash.as_bytes());
        }
        self.actions.bind(transcript);
        Ok(())
    }

    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr])
        -> Result<[Fr; 4], String>
    {
        if r.len() != self.row_log || u.len() != self.input_log || v.len() != self.input_log {
            return Err("native work coefficient dimensions differ".into());
        }
        let mut result = [Fr::zero(); 4];
        for tag in 0..6 {
            let d = self.source_row_logs[tag];
            let weight = wiring::eq_index(&r[self.local_row_log..], tag)
                * r[d..self.local_row_log].iter().fold(Fr::one(), |a, x| a * (Fr::one() - x));
            let coefficients = match tag {
                0 => self.actions.coefficients(&r[..d], u, v)?,
                1 => work_tree_work::local_coefficients(self.parent.work_boundary(), &r[..d], u, v)?,
                2..=4 => self.links[tag - 2].coefficients(self.parent.descriptor(), &r[..d], u, v)?,
                5 => self.alias.coefficients(self.parent.descriptor(), &r[..d], u, v)?,
                _ => unreachable!(),
            };
            for (sum, coefficient) in result.iter_mut().zip(coefficients) {
                *sum += weight * coefficient;
            }
        }
        Ok(result)
    }

    fn send(&self, tag: usize, mut term: Term, count: &mut usize,
        sink: &mut impl FnMut(Term) -> Result<(), String>) -> Result<(), String>
    {
        let input_len = 1usize << self.input_log;
        if term.row >= 1usize << self.source_row_logs[tag]
            || term.gate.left >= input_len || term.gate.right >= input_len
        {
            return Err("native work source term outside fixed family domain".into());
        }
        term.row = term.row.checked_add(tag.checked_shl(self.local_row_log as u32)
            .ok_or("native work tag shift overflow")?).ok_or("native work row overflow")?;
        let next = count.checked_add(1).ok_or("native work term count overflow")?;
        sink(term)?;
        *count = next;
        Ok(())
    }

    pub(crate) fn visit_terms(&self, mut sink: impl FnMut(Term) -> Result<(), String>)
        -> Result<usize, String>
    {
        let mut count = 0usize;
        for owner in 0..self.parent.slots() {
            self.actions.visit_owner(owner, |term| self.send(0, term, &mut count, &mut sink))?;
        }
        for owner in 0..self.parent.slots() {
            let mut failure = None;
            self.parent.work_boundary().emit_slot(owner, |term| {
                if failure.is_none() {
                    if let Err(error) = self.send(1, term, &mut count, &mut sink) {
                        failure = Some(error);
                    }
                }
            })?;
            if let Some(error) = failure { return Err(error); }
        }
        for (index, family) in self.links.iter().chain(std::iter::once(self.alias)).enumerate() {
            family.emit_terms(self.parent.descriptor(), |term| {
                self.send(index + 2, term, &mut count, &mut sink)
            })?;
        }
        Ok(count)
    }
}
