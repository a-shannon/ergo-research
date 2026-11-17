//! Bounded physical point-bank projection from the existing H21 native frame.
//! The ignored frame test authenticates two rows only, not common-X PCS or a proof.
use super::*;
use ark_ff::One;
use std::os::windows::fs::MetadataExt;

fn point_bit(bytes: &[u8], wire: usize) -> bool {
    (bytes[wire / 8] >> (wire % 8)) & 1 != 0
}

fn bool_point(width: usize, index: usize) -> Vec<Fr> {
    (0..width).map(|bit| Fr::from(((index >> bit) & 1) as u64)).collect()
}

fn dense_weight(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |weight, (bit, coordinate)| {
        if (index >> bit) & 1 == 1 {
            weight * coordinate
        } else {
            weight * (Fr::one() - coordinate)
        }
    })
}

#[test]
#[ignore = "one-use pinned H21 frame run requires source pins and bounded runner review"]
fn c330_h21_role3_actual_source_projection() -> Result<(), String> {
    if std::env::var("NIPOPOW_C330_ROLE3_ACTUAL").as_deref() != Ok("1") {
        return Err("explicit C330 actual-source mode required".into());
    }
    let path = std::env::var_os("NIPOPOW_H21_FRAME")
        .ok_or("pinned H21 frame path required")?;
    let path = Path::new(&path);
    if !path.is_absolute() {
        return Err("H21 frame path must be absolute".into());
    }
    let before = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !before.is_file() || before.file_attributes() & 0x400 != 0
        || before.len() != FRAME_BYTES {
        return Err("H21 frame must be exact regular non-reparse file".into());
    }
    let file = File::open(path).map_err(|e| e.to_string())?;
    if file.metadata().map_err(|e| e.to_string())?.len() != FRAME_BYTES {
        return Err("opened H21 frame length changed".into());
    }
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)?;
    preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("H21 frame RAW records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("H21 frame prefix/extension census differs".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;
    let after = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if after.len() != before.len() || after.modified().map_err(|e| e.to_string())?
        != before.modified().map_err(|e| e.to_string())? {
        return Err("H21 frame changed during read".into());
    }

    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())?;
    validate_native_plan_input(&plan, &prefix)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let projection = producer.h21_point_projection()?;
    for owner in [844_672usize, (1 << 21) - 1] {
        let row = producer.produce(owner)?;
        row.validate_identity_for_history_test(&plan, &prefix, owner)?;
        if row.packed_bytes().len() != OWNER_ROW_BYTES {
            return Err("H21 owner row byte width".into());
        }
        let height = (owner + 1).min(N);
        let header = prefix.header(height)?;
        let fields = crate::serializer::Fields::from_header(&header)?;
        let witness = crate::point_membership::witness(fields.pk, fields.w)?;
        if witness.len() != 8192 {
            return Err("point witness width".into());
        }
        let mut bank = Vec::with_capacity(8192);
        for local in 0..8192usize {
            let global = projection.global_wire(owner, local)?;
            if global != (owner << 20) + 786_432 + local {
                return Err("producer-owned H21 point global address".into());
            }
            let bit = point_bit(row.packed_bytes(), global % OWNER_ROW_BITS);
            if bit != witness[local] {
                return Err(format!("H21 point source bit differs owner={owner} local={local}"));
            }
            bank.push(Fr::from(bit as u64));
        }

        // A Boolean owner selector and the seven fixed bank coordinates reduce
        // common-X evaluation to this one dense 8192-bit column.
        let local_point: Vec<_> = (0..13).map(|bit| Fr::from((bit + 2) as u64)).collect();
        let point = [local_point.clone(), bool_point(21, owner)].concat();
        let projected = projection.project(&point)?;
        let manual: Fr = bank.iter().enumerate().map(|(local, bit)| {
            *bit * dense_weight(&local_point, local)
        }).sum();
        let folded = crate::gkr::mle(&bank, &local_point).map_err(|e| e.to_string())?;
        if manual != folded {
            return Err("independent dense point-bank MLE differs".into());
        }
        for local in [0, 1, 4095, 8191] {
            let boolean = [bool_point(13, local), bool_point(21, owner)].concat();
            if projection.project(&boolean)? != bool_point(41,
                projection.global_wire(owner, local)?) {
                return Err("Boolean common-X projection differs".into());
            }
        }
        if projected.len() != 41 || projected[13..20]
            != [Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::one(), Fr::one()] {
            return Err("H21 fixed point-bank coordinates differ".into());
        }

        // Mutate exactly one of the seven fixed coordinates. Select a local
        // position where the actual alternate bank differs, so the negative
        // result cannot depend on a probabilistic field cancellation.
        let mut isolated = None;
        for bank_bit in 0..7usize {
            let alternate = 786_432usize ^ (1 << (13 + bank_bit));
            for local in 0..8192usize {
                let point_bit_value = point_bit(row.packed_bytes(), 786_432 + local);
                let other_bit_value = point_bit(row.packed_bytes(), alternate + local);
                if point_bit_value != other_bit_value {
                    isolated = Some((bank_bit, local, point_bit_value, other_bit_value,
                        alternate));
                    break;
                }
            }
            if isolated.is_some() { break; }
        }
        let (bank_bit, local, expected, wrong, alternate) = isolated
            .ok_or("no isolated alternate-bank difference in actual source row")?;
        let boolean = [bool_point(13, local), bool_point(21, owner)].concat();
        let correct = projection.project(&boolean)?;
        let mut mutant = correct.clone();
        mutant[13 + bank_bit] = Fr::one() - mutant[13 + bank_bit];
        if correct != bool_point(41, projection.global_wire(owner, local)?)
            || mutant != bool_point(41, (owner << 20) + alternate + local)
            || expected == wrong {
            return Err("single-coordinate point-bank mutant not isolated".into());
        }
    }
    println!("C330_ROLE3_ACTUAL_PASS owners=[844672,2097151] point_bits_per_owner=8192 input34_to_x41=true dense_mle=true isolated_bank_mutant=true full_proof=false");
    Ok(())
}
