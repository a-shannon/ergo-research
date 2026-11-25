//! Exact pinned RAW nBits -> full scheduled suffix MAX -> selected physical Cap.
//! Canonical admission reuses adjudicated c78 on the same frame/parser closure;
//! this height-only decoding pass is not a new parent/genesis/reencode proof.
use super::*;
use crate::h21_scheduled_max_cap::{OwnerCells, Prepared, Writer};
use ark_ff::One;
use std::cell::{Cell, RefCell};

const FIRST: usize = 844672;
const LAST: usize = 1827840;
const TERMINAL: [usize; 2] = [1827840, 1827775];
const START: [usize; 3] = [844672, 844673, 844801];
const MAX_OWNER: [usize; 3] = [844670, 844798, 844926];
const MAX_BASE: [usize; 2] = [999424, 1000097];
const CAP_BASE: [usize; 2] = [1000770, 1002818];
const CAP_GUARD: [usize; 2] = [845759, 845887];
const D_BASE: usize = 987674;
fn coordinate(owner: usize, local: usize) -> usize {
    owner * 1048576 + local
}
fn decode(bits: &[u32], height: usize) -> Result<BigUint, String> {
    let compact = *bits
        .get(height.checked_sub(1).ok_or("native D height zero")?)
        .ok_or("native D height extent")?;
    crate::work_tree_work::native_decode(compact)
        .map_err(|e| format!("native D height={height}: {e}"))
}

struct NativeDs<'a> {
    bits: &'a [u32],
    next: usize,
    last: &'a Cell<usize>,
    error: &'a RefCell<Option<String>>,
}
impl Iterator for NativeDs<'_> {
    type Item = (usize, BigUint);
    fn next(&mut self) -> Option<Self::Item> {
        if self.next > LAST {
            return None;
        }
        let height = self.next;
        self.next += 1;
        self.last.set(height);
        match decode(self.bits, height) {
            Ok(d) => Some((height, d)),
            Err(e) => {
                *self.error.borrow_mut() = Some(e);
                self.next = LAST + 1;
                None
            }
        }
    }
}
#[derive(Clone, Copy)]
enum Stream {
    Full,
    DropFirst,
    Surplus,
}
fn prepare(bits: &[u32], mode: Stream) -> Result<Prepared, String> {
    let last = Cell::new(0);
    let error = RefCell::new(None);
    let input = NativeDs {
        bits,
        next: FIRST,
        last: &last,
        error: &error,
    };
    let result = match mode {
        Stream::Full => Prepared::from_d_iter(input),
        Stream::DropFirst => Prepared::from_d_iter(input.skip(1)),
        Stream::Surplus => Prepared::from_d_iter(input.chain([(LAST + 1, BigUint::from(1u8))])),
    };
    if let Some(e) = error.into_inner() {
        return Err(e);
    }
    result.map_err(|e| {
        if e == "scheduled D changes within epoch" {
            format!("{e}; first_offending_height={}", last.get())
        } else {
            format!("{e}; last_yielded_native_height={}", last.get())
        }
    })
}

struct Oracle {
    r: [[BigUint; 3]; 2],
    terminal: [BigUint; 2],
    peak_height: [[usize; 3]; 2],
}
fn oracle(bits: &[u32]) -> Result<Oracle, String> {
    let mut running: [BigUint; 2] = std::array::from_fn(|_| BigUint::from(0u8));
    let mut peak = [0usize; 2];
    let mut out = Oracle {
        r: std::array::from_fn(|_| std::array::from_fn(|_| BigUint::from(0u8))),
        terminal: [decode(bits, TERMINAL[0])?, decode(bits, TERMINAL[1])?],
        peak_height: [[0; 3]; 2],
    };
    // One reverse pass over EVERY D height, not Plan epochs or Prepared internals.
    for height in (FIRST..=LAST).rev() {
        let d = decode(bits, height)?;
        for c in 0..2 {
            if height <= TERMINAL[c] {
                if d > running[c] {
                    running[c] = d.clone();
                    peak[c] = height;
                }
                if let Some(j) = START.iter().position(|h| *h == height) {
                    out.r[c][j] = running[c].clone();
                    out.peak_height[c][j] = peak[c];
                }
            }
        }
    }
    Ok(out)
}
fn reference_cap(r: &BigUint) -> Result<BigUint, String> {
    // Positive integer division and repeated doubling, independent of cap scalar.
    let p = (r * BigUint::from(3u8)) / BigUint::from(2u8);
    if r.is_zero() {
        return Err("oracle positive MAX.R".into());
    }
    let mut q = BigUint::from(1u8);
    let mut exponent = 0;
    while q < p {
        q *= BigUint::from(2u8);
        exponent += 1;
        if exponent > 64 {
            return Err("oracle Cap coverage".into());
        }
    }
    Ok(q)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Source {
    Scheduled(Writer),
    NativeD { height: usize },
}
#[derive(Clone, Copy, Debug)]
struct Domain {
    owner: usize,
    start: usize,
    width: usize,
    source: Source,
}
impl Domain {
    fn validate(&self) -> Result<(), String> {
        let (owner, start, width) = match self.source {
            Source::Scheduled(Writer::Max { context, end }) if context < 2 => (
                end.checked_sub(2).ok_or("MAX height-owner underflow")?,
                MAX_BASE[context],
                673,
            ),
            Source::Scheduled(Writer::Cap { context, origin }) if context < 2 => (
                origin.checked_sub(1).ok_or("Cap origin-owner underflow")?,
                CAP_BASE[context],
                2048,
            ),
            Source::NativeD { height } => (
                height
                    .checked_sub(2)
                    .ok_or("native D height-owner underflow")?,
                D_BASE,
                224,
            ),
            _ => return Err("typed source context".into()),
        };
        if (self.owner, self.start, self.width) != (owner, start, width) {
            return Err("typed source owner/context/domain".into());
        }
        Ok(())
    }
}
#[derive(Clone, Default)]
struct Physical {
    cells: BTreeMap<usize, Fr>,
    sources: BTreeMap<usize, Source>,
}
impl Physical {
    fn insert(&mut self, domain: Domain, values: &[Fr]) -> Result<(), String> {
        domain.validate()?;
        if values.len() != domain.width || values.iter().any(|b| !b.is_zero() && !b.is_one()) {
            return Err("physical Boolean domain width".into());
        }
        if (0..domain.width).any(|k| {
            self.cells
                .contains_key(&coordinate(domain.owner, domain.start + k))
        }) {
            return Err("duplicate physical writer".into());
        }
        for (k, value) in values.iter().enumerate() {
            let at = coordinate(domain.owner, domain.start + k);
            self.cells.insert(at, *value);
            self.sources.insert(at, domain.source);
        }
        Ok(())
    }
    fn read(&self, index: usize) -> Result<Fr, String> {
        self.cells
            .get(&index)
            .copied()
            .ok_or_else(|| format!("missing physical X={index}"))
    }
    fn word(&self, owner: usize, start: usize, width: usize) -> Result<BigUint, String> {
        let mut out = BigUint::from(0u8);
        for k in 0..width {
            let b = self.read(coordinate(owner, start + k))?;
            if !b.is_zero() && !b.is_one() {
                return Err("physical nonboolean read".into());
            }
            if b.is_one() {
                out += BigUint::from(1u8) << k;
            }
        }
        Ok(out)
    }
}
fn physical(prepared: &Prepared, bits: &[u32]) -> Result<(Physical, Vec<Domain>), String> {
    let mut out = Physical::default();
    let mut domains = Vec::new();
    for owner in [844670, 844798, 844926, 1827838, 1827773, 845759, 845887] {
        let mut cells = OwnerCells::new(owner)?;
        prepared.owner_patch(owner)?.apply(&mut cells)?;
        let mut writers = BTreeSet::new();
        prepared.plan().visit_owner(owner, |w, _| {
            writers.insert(w);
            Ok(())
        })?;
        for writer in writers {
            let (start, width) = match writer {
                Writer::Max { context, .. } => (MAX_BASE[context], 673),
                Writer::Cap { context, .. } => (CAP_BASE[context], 2048),
            };
            let domain = Domain {
                owner,
                start,
                width,
                source: Source::Scheduled(writer),
            };
            let values = (0..width)
                .map(|k| cells.read(start + k))
                .collect::<Result<Vec<_>, _>>()?;
            out.insert(domain, &values)?;
            domains.push(domain);
        }
    }
    for height in [844672, 844800, 1827840, 1827775] {
        let d = decode(bits, height)?;
        let domain = Domain {
            owner: height - 2,
            start: D_BASE,
            width: 224,
            source: Source::NativeD { height },
        };
        let values = (0..224)
            .map(|k| Fr::from(u64::from(d.bit(k as u64))))
            .collect::<Vec<_>>();
        out.insert(domain, &values)?;
        domains.push(domain);
    }
    Ok((out, domains))
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Selected {
    writer: Writer,
    term: crate::sparse::Term,
}
fn selected(prepared: &Prepared) -> Result<Vec<Selected>, String> {
    let mut out = Vec::with_capacity(41368);
    for owner in [844670, 844798, 1827838, 1827773, 845759, 845887] {
        prepared.plan().visit_owner(owner, |writer, term| {
            let keep = match writer {
                Writer::Max { context, end } => {
                    [844670, 844798].contains(&owner)
                        || (context == 0 && owner == 1827838 && end == 1827840)
                        || (context == 1 && owner == 1827773 && end == 1827775)
                }
                Writer::Cap { .. } => CAP_GUARD.contains(&owner),
            };
            if keep {
                out.push(Selected { writer, term });
            }
            Ok(())
        })?;
    }
    Ok(out)
}
fn residuals(actual: &[Selected], expected: &[Selected], x: &Physical) -> Result<(), String> {
    // Coordinate/Writer census precedes arithmetic, so equal context values
    // cannot make a wrong provenance or an omitted source relation acceptable.
    if actual != expected {
        return Err("tuple provenance/count".into());
    }
    let mut rows = BTreeMap::<usize, Fr>::new();
    for t in actual {
        let g = &t.term.gate;
        // Only zero-coefficient operands are skipped. Missing real reads fail;
        // no unassigned native or successor cell gets a zero fallback.
        let a = if !g.c1.is_zero() || !g.c3.is_zero() {
            x.read(g.left)?
        } else {
            Fr::zero()
        };
        let b = if !g.c2.is_zero() || !g.c3.is_zero() {
            x.read(g.right)?
        } else {
            Fr::zero()
        };
        *rows.entry(t.term.row).or_insert(Fr::zero()) += g.c0 + g.c1 * a + g.c2 * b + g.c3 * a * b;
    }
    let expected_rows = expected.iter().map(|t| t.term.row).collect::<BTreeSet<_>>();
    if rows.len() != expected_rows.len() {
        return Err(format!("selected support census {}", rows.len()));
    }
    if let Some((row, _)) = rows.iter().find(|(_, v)| !v.is_zero()) {
        return Err(format!("physical residual ROW={row}"));
    }
    Ok(())
}
fn marker(text: &str) -> Result<(), String> {
    println!("{text}");
    std::io::stdout().flush().map_err(|e| e.to_string())
}

#[test]
#[ignore = "full pinned ERFV nBits, reviewed canonicality reuse and 2GiB/240s Job required"]
fn native_d_scheduled_max_cap_selected_sources() -> Result<(), String> {
    let started = Instant::now();
    let path = std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned frame environment variable")?;
    let path = Path::new(&path);
    assert!(path.is_absolute());
    let before = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES);
    let file = File::open(path).map_err(|e| e.to_string())?;
    assert_eq!(
        file.metadata().map_err(|e| e.to_string())?.len(),
        FRAME_BYTES
    );
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)?;
    preamble(&mut frame, 1827839, N as u32)?;
    let mut bits = Vec::with_capacity(N);
    let extensions = {
        let mut headers = HeaderIter::new(&mut frame, N);
        for (index, raw) in headers.by_ref().enumerate() {
            let height = index + 1;
            let raw = raw?;
            let header = ergo_header_core::Header::decode(&raw, None)
                .map_err(|e| format!("RAW decode height={height}: {e:?}"))?;
            if header.height != height as u32 {
                return Err(format!("decoded height mismatch at record={height}"));
            }
            bits.push(header.n_bits);
        }
        assert_eq!(headers.remaining, 0);
        headers.extensions
    };
    assert_eq!(bits.len(), N);
    assert_eq!(frame.offset, PREFIX_BYTES);
    assert_eq!(extensions, EXTENSIONS);
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;
    let after = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES);
    assert_eq!(
        after.modified().map_err(|e| e.to_string())?,
        before.modified().map_err(|e| e.to_string())?
    );
    // Reused evidence: original receipt4C1C...BD82B (still HOLD), independent
    // adjudicationA011...EA39, same SHA frame and byte-identical parser/header-core.
    marker(&format!("C126A_FRAME records={} extensions={extensions} full_frame_sha256_verified=true canonicality_reused=c78 new_canonical_admission=false extraction_s={:.6}",bits.len(),started.elapsed().as_secs_f64()))?;

    let phase = Instant::now();
    let prepared = prepare(&bits, Stream::Full)?;
    let prepare_seconds = phase.elapsed().as_secs_f64();
    let dropped = match prepare(&bits, Stream::DropFirst) {
        Ok(_) => return Err("dropped first real D accepted".into()),
        Err(e) => e,
    };
    assert!(dropped.contains("height/order"));
    let surplus = match prepare(&bits, Stream::Surplus) {
        Ok(_) => return Err("surplus real D accepted".into()),
        Err(e) => e,
    };
    assert!(surplus.contains("surplus"));
    marker(&format!("C126A_D heights=983169 first={FIRST} last={LAST} epoch_constancy_checked=true dropped_first_rejected=true surplus_rejected=true from_d_iter_s={prepare_seconds:.6}"))?;

    let phase = Instant::now();
    let oracle = oracle(&bits)?;
    marker(&format!("C126A_ORACLE height_evaluations=983169 reverse_passes=1 contexts=2 scalar_suffixes=6 oracle_s={:.6}",phase.elapsed().as_secs_f64()))?;
    let phase = Instant::now();
    let (x, domains) = physical(&prepared, &bits)?;
    for c in 0..2 {
        for j in 0..3 {
            let actual = x.word(MAX_OWNER[j], MAX_BASE[c], 224)?;
            assert_eq!(actual, oracle.r[c][j]);
            for k in 0..224 {
                assert_eq!(
                    x.read(coordinate(MAX_OWNER[j], MAX_BASE[c] + k))?,
                    Fr::from(u64::from(oracle.r[c][j].bit(k as u64)))
                );
            }
        }
        for j in 0..2 {
            assert_eq!(
                x.word(MAX_OWNER[j], MAX_BASE[c] + 224, 224)?,
                oracle.r[c][j + 1],
                "next-R link"
            );
            let native = decode(&bits, [844672, 844800][j])?;
            assert_eq!(x.word(MAX_OWNER[j], D_BASE, 224)?, native);
            assert_eq!(
                x.word(CAP_GUARD[j], CAP_BASE[c] + 1, 224)?,
                oracle.r[c][j],
                "Cap actual imported operand"
            );
            assert_eq!(
                x.word(CAP_GUARD[j], CAP_BASE[c] + 225, 224)?,
                oracle.r[c][j]
            );
            let q = reference_cap(&oracle.r[c][j])?;
            assert_eq!(x.word(CAP_GUARD[j], CAP_BASE[c] + 740, 65)?, q);
            println!("C126A_SELECTED context={c} source_owner={} suffix_start={} terminal={} argmax_height={} cap_guard={} r={} v={q}",MAX_OWNER[j],START[j],TERMINAL[c],oracle.peak_height[c][j],CAP_GUARD[j],oracle.r[c][j]);
        }
        let owner = TERMINAL[c] - 2;
        assert_eq!(x.word(owner, MAX_BASE[c], 224)?, oracle.terminal[c]);
        assert_eq!(x.word(owner, MAX_BASE[c] + 224, 224)?, BigUint::from(0u8));
        assert_eq!(x.word(owner, D_BASE, 224)?, oracle.terminal[c]);
    }
    let terms = selected(&prepared)?;
    assert_eq!(terms.len(), 41368);
    assert_eq!(
        terms
            .iter()
            .map(|t| t.term.row)
            .collect::<BTreeSet<_>>()
            .len(),
        16744
    );
    residuals(&terms, &terms, &x)?;
    // Typed native height and scheduled MAX context checks remain decisive even
    // if different epochs/contexts contain the same D/R numerical value.
    let native = *domains
        .iter()
        .find(|d| d.source == Source::NativeD { height: 844672 })
        .unwrap();
    let mut bad = native;
    bad.owner += 1;
    assert!(bad.validate().is_err());
    let max = *domains
        .iter()
        .find(|d| {
            d.source
                == Source::Scheduled(Writer::Max {
                    context: 0,
                    end: 844672,
                })
        })
        .unwrap();
    let mut bad = max;
    bad.source = Source::Scheduled(Writer::Max {
        context: 1,
        end: 844672,
    });
    assert!(bad.validate().is_err());
    let mut bad = max;
    bad.owner += 1;
    assert!(bad.validate().is_err());
    // Actual tuple context mutation is rejected before any equal-value residual.
    let index = terms
        .iter()
        .position(|p| {
            matches!(p.writer, Writer::Cap { context: 0, .. })
                && p.term.gate.left == coordinate(844670, 999424)
        })
        .unwrap();
    let mut bad = terms.clone();
    bad[index].term.gate.left = coordinate(844670, 1000097);
    assert!(residuals(&bad, &terms, &x)
        .unwrap_err()
        .contains("provenance"));
    let mut bad = terms.clone();
    bad.remove(index);
    assert!(residuals(&bad, &terms, &x)
        .unwrap_err()
        .contains("provenance"));
    // Separate missing successor and missing imported MAX.R; real reads fail.
    let mut bad = x.clone();
    for k in 0..224 {
        bad.cells.remove(&coordinate(844926, MAX_BASE[0] + k));
    }
    assert!(residuals(&terms, &terms, &bad)
        .unwrap_err()
        .contains("missing physical"));
    let cap_terms = terms
        .iter()
        .filter(|t| matches!(t.writer, Writer::Cap { .. }))
        .cloned()
        .collect::<Vec<_>>();
    residuals(&cap_terms, &cap_terms, &x)?;
    let mut bad = x.clone();
    for k in 0..224 {
        bad.cells.remove(&coordinate(844670, MAX_BASE[0] + k));
    }
    // The honest Cap-only subset passed first; only its imported R is removed.
    assert!(residuals(&cap_terms, &cap_terms, &bad)
        .unwrap_err()
        .contains("missing physical"));
    for at in [
        coordinate(844670, D_BASE),
        coordinate(844670, MAX_BASE[0]),
        coordinate(845759, CAP_BASE[0] + 740),
    ] {
        let mut bad = x.clone();
        let value = bad.cells.get_mut(&at).ok_or("mutant cell absent")?;
        *value = Fr::one() - *value;
        assert!(residuals(&terms, &terms, &bad)
            .unwrap_err()
            .contains("physical residual"));
    }
    marker(&format!("C126A_LOCAL_PASS max_complete_relations=6 cap_relations=4 lookup_only_owner=844926 terms={} rows=16744 all_residuals_zero=true typed_and_real_x_negatives=true local_s={:.6} elapsed_s={:.6} pow_daa_proof=false global_witness=false",terms.len(),phase.elapsed().as_secs_f64(),started.elapsed().as_secs_f64()))?;
    Ok(())
}
