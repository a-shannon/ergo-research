//! Scalar, code-owned exports for foreign inputs read by native owner producers.
//!
//! This module only exposes typed values already present in `NativePrefix`.
//! It does not construct owner rows or certify their incident relations.
use std::collections::BTreeMap;

use crate::{
    header_hash::SERIALIZER_OFFSET,
    packed_owner_assembly::{validate_native_plan_input, NativePrefix},
    serializer,
    work_tree_fixed_hash::{self as fixed, Role as FixedRole},
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::{self as layout, WIDTH},
    work_tree_work,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SerializerPort {
    Byte { byte: usize, bit: usize },
    Length { bit: usize },
    Timestamp { bit: usize },
    NBits { bit: usize },
    Height { bit: usize },
}

/// A checked scalar view over the immutable native prefix.
pub(crate) struct NativeExports<'a> {
    plan: &'a WorkTreeHistoryPlan,
    input: &'a NativePrefix,
    serializer_input_len: usize,
    serializer_ports: BTreeMap<usize, Vec<SerializerPort>>,
    total_input_len: usize,
}

impl<'a> NativeExports<'a> {
    pub(crate) fn new(
        plan: &'a WorkTreeHistoryPlan,
        input: &'a NativePrefix,
    ) -> Result<Self, String> {
        if plan.headers() != 3073
            || plan.slot_log() != 12
            || plan.slots() != 4096
            || plan.descriptor().root != input.root()
            || plan.work_profile().total_be28 != input.total_be28()
            || plan.descriptor().genuine != 3072
            || plan.descriptor().leaves != 4096
        {
            return Err("native exports require the admitted N3073/S12 prefix".into());
        }
        Self::new_for_history(plan, input)
    }

    pub(crate) fn new_for_history(
        plan: &'a WorkTreeHistoryPlan,
        input: &'a NativePrefix,
    ) -> Result<Self, String> {
        validate_native_plan_input(plan, input)?;

        let compiled = serializer::build(None)?;
        if compiled.circuit.input_len != crate::header_hash::SERIALIZER_WIDTH {
            return Err("native export serializer width changed".into());
        }
        let mut serializer_ports = BTreeMap::<usize, Vec<SerializerPort>>::new();
        let mut add = |wire: usize, port: SerializerPort| -> Result<(), String> {
            if wire >= compiled.circuit.input_len {
                return Err("native export serializer port outside declared input".into());
            }
            serializer_ports.entry(wire).or_default().push(port);
            Ok(())
        };
        for (byte, bits) in compiled.layout.bytes.iter().enumerate() {
            for (bit, &wire) in bits.iter().enumerate() {
                add(wire, SerializerPort::Byte { byte, bit })?;
            }
        }
        for (bit, &wire) in compiled.layout.length.iter().enumerate() {
            add(wire, SerializerPort::Length { bit })?;
        }
        for (bit, &wire) in compiled.layout.fields.timestamp.iter().enumerate() {
            add(wire, SerializerPort::Timestamp { bit })?;
        }
        for (bit, &wire) in compiled.layout.fields.n_bits.iter().enumerate() {
            add(wire, SerializerPort::NBits { bit })?;
        }
        for (bit, &wire) in compiled.layout.fields.height.iter().enumerate() {
            add(wire, SerializerPort::Height { bit })?;
        }

        let total_input_len = plan
            .slots()
            .checked_mul(WIDTH)
            .ok_or("native export global input width overflow")?;
        Ok(Self {
            plan,
            input,
            serializer_input_len: compiled.circuit.input_len,
            serializer_ports,
            total_input_len,
        })
    }

    /// Read one coordinate in the bound native history input; unsupported coordinates fail closed.
    pub(crate) fn bit(&self, index: usize) -> Result<bool, String> {
        if index == 0 {
            // The circuit's dedicated global constant wire is code-owned false.
            return Ok(false);
        }
        if index >= self.total_input_len {
            if self.plan.headers() == 3073 && self.plan.slot_log() == 12 && self.plan.slots() == 4096 {
                return Err(format!("native export coordinate outside N3073: {index}"));
            }
            return Err(format!("native export coordinate outside bound history: {index}"));
        }
        let owner = index / WIDTH;
        let local = index % WIDTH;
        let serializer_end = SERIALIZER_OFFSET
            .checked_add(self.serializer_input_len)
            .ok_or("native export serializer end overflow")?;
        if (SERIALIZER_OFFSET..serializer_end).contains(&local) {
            let coordinate = local - SERIALIZER_OFFSET;
            let ports = self
                .serializer_ports
                .get(&coordinate)
                .ok_or_else(|| format!("unsupported serializer internal coordinate {index}"))?;
            let source_owner = owner.min(self.input.header_count() - 1);
            let height = source_owner + 1;
            let raw = self.input.raw(height)?;
            let mut value = None;
            for &port in ports {
                let next = match port {
                    SerializerPort::Byte { byte, bit } => {
                        raw.get(byte).is_some_and(|value| (value >> bit) & 1 != 0)
                    }
                    SerializerPort::Length { bit } => (raw.len() >> bit) & 1 != 0,
                    SerializerPort::Timestamp { bit } => {
                        ((self.input.timestamp(height)? as u64) >> bit) & 1 != 0
                    }
                    SerializerPort::NBits { bit } => {
                        (self.input.compact_n_bits(height)? >> bit) & 1 != 0
                    }
                    SerializerPort::Height { bit } => (height >> bit) & 1 != 0,
                };
                if value.is_some_and(|previous| previous != next) {
                    return Err(format!("serializer port collision disagrees at {index}"));
                }
                value = Some(next);
            }
            return value.ok_or_else(|| format!("empty serializer port map at {index}"));
        }

        let endpoint_end = layout::ENDPOINT_BASE
            .checked_add(layout::ENDPOINT_WIDTH)
            .ok_or("native export endpoint end overflow")?;
        if (layout::ENDPOINT_BASE..endpoint_end).contains(&local) {
            return self.endpoint_bit(owner, local);
        }
        Err(format!("unsupported foreign coordinate {index}"))
    }

    fn endpoint_bit(&self, slot: usize, local: usize) -> Result<bool, String> {
        let endpoints = &layout::shared_baseline()?.endpoints;
        let genuine = self.plan.descriptor().genuine;
        let role = self.plan.fixed_profile().role(slot)?;

        if let Some(bit) = in_wires(&endpoints.raw, local) {
            return Ok(slot < genuine && byte_bit(self.input.raw(slot + 2)?, bit));
        }
        if let Some(bit) = in_wires(&endpoints.length, local) {
            let length = if slot < genuine {
                self.input.raw(slot + 2)?.len()
            } else {
                0
            };
            return Ok((length >> bit) & 1 != 0);
        }
        if let Some(bit) = in_wires(&endpoints.n_bits, local) {
            let value = if slot < genuine {
                self.input.compact_n_bits(slot + 2)?
            } else {
                0
            };
            return Ok((value >> bit) & 1 != 0);
        }
        if let Some(bit) = in_wires(&endpoints.height, local) {
            return Ok(slot < genuine && (((slot + 2) >> bit) & 1 != 0));
        }
        if let Some(bit) = in_wires(&endpoints.lower, local) {
            return if slot < genuine {
                let (lower, _) = self.input.interval(slot + 2)?;
                Ok(be224_bit(&lower, bit))
            } else {
                Ok(false)
            };
        }
        if let Some(bit) = in_wires(&endpoints.upper, local) {
            return if slot < genuine {
                let (_, upper) = self.input.interval(slot + 2)?;
                Ok(be224_bit(&upper, bit))
            } else {
                Ok(false)
            };
        }
        if let Some(bit) = in_wires(&endpoints.work, local) {
            if slot >= genuine {
                return Ok(false);
            }
            let compact = self.input.compact_n_bits(slot + 2)?;
            let value = work_tree_work::native_decode(compact)?;
            return Ok(value.bit(bit as u64));
        }
        if let Some(bit) = in_wires(&endpoints.work_minus_one, local) {
            if slot >= genuine {
                return Ok(false);
            }
            let compact = self.input.compact_n_bits(slot + 2)?;
            let value = work_tree_work::native_decode(compact)?;
            return Ok((value - num_bigint::BigUint::from(1u8)).bit(bit as u64));
        }
        if let Some(bit) = in_wires(&endpoints.exponent, local) {
            let exponent = if slot < genuine {
                (self.input.compact_n_bits(slot + 2)? >> 24) as usize
            } else {
                usize::MAX
            };
            return Ok(exponent == bit);
        }
        if let Some(bit) = in_wires(&endpoints.leaf, local) {
            return if role == FixedRole::Dummy {
                Ok(false)
            } else {
                Ok(byte_bit(&self.input.leaf_digest(slot)?, bit))
            };
        }

        if let Some(bit) = in_wires(&endpoints.node_left, local) {
            return match role {
                FixedRole::Node { level, position } => {
                    let child_base = if level == 1 {
                        0
                    } else {
                        self.plan.descriptor().level(level as usize - 1)?.0
                    };
                    let child = child_base + 2 * position as usize;
                    let digest = if level == 1 {
                        self.input.leaf_digest(child)?
                    } else {
                        self.input.node_digest(child)?
                    };
                    Ok(byte_bit(&digest, bit))
                }
                FixedRole::Profile => Ok(false),
                FixedRole::Dummy => Ok(false),
            };
        }
        if let Some(bit) = in_wires(&endpoints.node_right, local) {
            return match role {
                FixedRole::Node { level, position } => {
                    let child_base = if level == 1 {
                        0
                    } else {
                        self.plan.descriptor().level(level as usize - 1)?.0
                    };
                    let child = child_base + 2 * position as usize + 1;
                    let digest = if level == 1 {
                        self.input.leaf_digest(child)?
                    } else {
                        self.input.node_digest(child)?
                    };
                    Ok(byte_bit(&digest, bit))
                }
                FixedRole::Profile => Ok(false),
                FixedRole::Dummy => Ok(false),
            };
        }
        if let Some(bit) = in_wires(&endpoints.node, local) {
            return match role {
                FixedRole::Node { .. } | FixedRole::Profile => {
                    Ok(byte_bit(&self.input.node_digest(slot)?, bit))
                }
                FixedRole::Dummy => Ok(false),
            };
        }
        if let Some(bit) = in_wires(&endpoints.profile, local) {
            return Ok(role != FixedRole::Dummy && byte_bit(&self.input.profile(), bit));
        }
        Err(format!(
            "unsupported typed endpoint coordinate {slot}:{local}"
        ))
    }
}

fn in_wires(wires: &[usize], local: usize) -> Option<usize> {
    let bit = local
        .checked_sub(*wires.first()?)
        .filter(|bit| *bit < wires.len())?;
    (wires.get(bit) == Some(&local)).then_some(bit)
}

fn byte_bit(bytes: &[u8], bit: usize) -> bool {
    bytes
        .get(bit / 8)
        .is_some_and(|byte| (byte >> (bit % 8)) & 1 != 0)
}

fn be224_bit(bytes: &[u8; 28], bit: usize) -> bool {
    (bytes[27 - bit / 8] >> (bit % 8)) & 1 != 0
}
