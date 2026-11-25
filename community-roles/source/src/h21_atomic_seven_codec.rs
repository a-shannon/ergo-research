use crate::{
    bank53_map::CutDescriptor,
    legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, Map},
    packed_owner_assembly::h21_structural_roster::PublicMapParameters,
};

pub(super) const MAX_PACKET_BYTES: usize = 192 * 1024;
pub(super) const MAX_STATEMENT_BYTES: usize = 8192;
pub(super) const MAX_COMMON_BYTES: usize = 65536;
pub(super) const KEY_BYTES: usize = 42864;
pub(super) const COMMITMENT_BYTES: usize = 384;
pub(super) const INPUT_BITS: [u8; 7] = [41, 41, 41, 34, 41, 41, 41];
pub(super) const ROW_BITS: [u8; 7] = [42, 40, 41, 35, 41, 30, 33];
pub(super) const GKR_BYTES: [usize; 7] = [9280, 9280, 9280, 7712, 9280, 9280, 9280];

const PACKET_MAGIC: &[u8; 8] = b"H21ATOM2";
const STATEMENT_MAGIC: &[u8; 8] = b"H21STMT1";
const VERSION: u8 = 1;
const PROFILE: u8 = 1;
const STATEMENT_BYTES: usize = 226;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct H21Statement {
    pub(super) root: [u8; 32],
    pub(super) total: [u8; 28],
    pub(super) tip: [u8; 32],
    pub(super) tip_time: i64,
    pub(super) parameters: [PublicMapParameters; 2],
}

#[derive(Clone)]
pub(super) struct DecodedH21Packet {
    pub(super) statement: H21Statement,
    pub(super) statement_bytes: Vec<u8>,
    pub(super) key: Vec<u8>,
    pub(super) commitment: Vec<u8>,
    pub(super) roles: [Vec<u8>; 7],
    pub(super) common: Vec<u8>,
}

fn validate_statement(statement: &H21Statement) -> Result<(), String> {
    let terminals = CutDescriptor::eligible08().terminals();
    for (index, parameter) in statement.parameters.iter().enumerate() {
        if parameter.terminal != terminals[index] {
            return Err("H21 statement cut terminal".into());
        }
        Map::new_modern_global_u_selected_lower(
            u64::try_from(parameter.terminal).map_err(|_| "H21 terminal conversion")?,
            21,
            parameter.exponent,
            parameter.lower,
        )?;
    }
    Ok(())
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_usize(out: &mut Vec<u8>, value: usize, what: &'static str) -> Result<(), String> {
    put_u64(out, u64::try_from(value).map_err(|_| what)?);
    Ok(())
}

fn lower_source_parts(source: LowerSource) -> (u8, u64) {
    match source {
        LowerSource::HeaderDifficulty { height } => (0, height),
        LowerSource::LegacyBound { q } => (1, q),
        LowerSource::InitialI => (2, 0),
        LowerSource::Reset417792 => (3, 0),
        LowerSource::Reset417793 => (4, 0),
    }
}

fn lower_branch_parts(branch: LowerBranch) -> Result<(u8, u64), String> {
    match branch {
        LowerBranch::Literal => Ok((0, 0)),
        LowerBranch::Equality => Ok((1, 0)),
        LowerBranch::Pivot(index) => Ok((2, u64::try_from(index)
            .map_err(|_| "H21 pivot conversion")?)),
    }
}

pub(super) fn encode_statement(statement: &H21Statement) -> Result<Vec<u8>, String> {
    validate_statement(statement)?;
    let mut out = Vec::with_capacity(STATEMENT_BYTES);
    out.extend_from_slice(STATEMENT_MAGIC);
    out.extend_from_slice(&[VERSION, 2, PROFILE, 0]);
    out.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
    put_u64(&mut out, crate::h21_snapshot::N as u64);
    out.extend_from_slice(&[21, 0, 0, 0]);
    out.extend_from_slice(&statement.root);
    out.extend_from_slice(&statement.total);
    out.extend_from_slice(&statement.tip);
    out.extend_from_slice(&statement.tip_time.to_le_bytes());
    for (context, parameter) in statement.parameters.iter().enumerate() {
        out.push(u8::try_from(context).map_err(|_| "H21 context conversion")?);
        put_usize(&mut out, parameter.terminal, "H21 terminal conversion")?;
        put_usize(&mut out, parameter.exponent, "H21 exponent conversion")?;
        let (source_tag, source_value) = lower_source_parts(parameter.lower.source);
        out.push(source_tag);
        put_u64(&mut out, source_value);
        let (branch_tag, branch_value) = lower_branch_parts(parameter.lower.branch)?;
        out.push(branch_tag);
        put_u64(&mut out, branch_value);
    }
    if out.len() != STATEMENT_BYTES || out.len() > MAX_STATEMENT_BYTES {
        return Err("H21 statement encoded extent".into());
    }
    Ok(out)
}

fn take<'a>(input: &'a [u8], offset: &mut usize, length: usize) -> Result<&'a [u8], String> {
    let end = offset.checked_add(length).ok_or("H21 offset overflow")?;
    let value = input.get(*offset..end).ok_or("H21 truncated input")?;
    *offset = end;
    Ok(value)
}

fn take_u64(input: &[u8], offset: &mut usize) -> Result<u64, String> {
    let bytes: [u8; 8] = take(input, offset, 8)?.try_into()
        .map_err(|_| "H21 integer extent")?;
    Ok(u64::from_le_bytes(bytes))
}

fn take_usize(input: &[u8], offset: &mut usize, what: &'static str) -> Result<usize, String> {
    usize::try_from(take_u64(input, offset)?).map_err(|_| what.into())
}

fn decode_source(tag: u8, value: u64) -> Result<LowerSource, String> {
    Ok(match tag {
        0 => LowerSource::HeaderDifficulty { height: value },
        1 => LowerSource::LegacyBound { q: value },
        2 if value == 0 => LowerSource::InitialI,
        3 if value == 0 => LowerSource::Reset417792,
        4 if value == 0 => LowerSource::Reset417793,
        2..=4 => return Err("H21 fixed source value must be zero".into()),
        _ => return Err("H21 lower source tag".into()),
    })
}

fn decode_branch(tag: u8, value: u64) -> Result<LowerBranch, String> {
    Ok(match tag {
        0 if value == 0 => LowerBranch::Literal,
        1 if value == 0 => LowerBranch::Equality,
        2 => LowerBranch::Pivot(usize::try_from(value)
            .map_err(|_| "H21 pivot conversion")?),
        0..=1 => return Err("H21 fixed branch value must be zero".into()),
        _ => return Err("H21 lower branch tag".into()),
    })
}

pub(super) fn decode_statement(input: &[u8]) -> Result<H21Statement, String> {
    if input.len() != STATEMENT_BYTES || input.len() > MAX_STATEMENT_BYTES {
        return Err("H21 statement extent".into());
    }
    let mut offset = 0usize;
    if take(input, &mut offset, 8)? != STATEMENT_MAGIC {
        return Err("H21 statement magic".into());
    }
    if take(input, &mut offset, 4)? != [VERSION, 2, PROFILE, 0] {
        return Err("H21 statement profile".into());
    }
    if take(input, &mut offset, 32)? != crate::header_order::MAINNET_GENESIS {
        return Err("H21 statement genesis".into());
    }
    if take_u64(input, &mut offset)? != crate::h21_snapshot::N as u64 {
        return Err("H21 statement history size".into());
    }
    if take(input, &mut offset, 4)? != [21, 0, 0, 0] {
        return Err("H21 statement slot geometry".into());
    }
    let root = take(input, &mut offset, 32)?.try_into()
        .map_err(|_| "H21 root extent")?;
    let total = take(input, &mut offset, 28)?.try_into()
        .map_err(|_| "H21 total extent")?;
    let tip = take(input, &mut offset, 32)?.try_into()
        .map_err(|_| "H21 tip extent")?;
    let tip_time = i64::from_le_bytes(take(input, &mut offset, 8)?.try_into()
        .map_err(|_| "H21 timestamp extent")?);
    let mut parameters = [
        PublicMapParameters { terminal: 0, exponent: 0,
            lower: LowerSelector { source: LowerSource::InitialI, branch: LowerBranch::Literal } },
        PublicMapParameters { terminal: 0, exponent: 0,
            lower: LowerSelector { source: LowerSource::InitialI, branch: LowerBranch::Literal } },
    ];
    for (context, parameter) in parameters.iter_mut().enumerate() {
        if take(input, &mut offset, 1)?[0] != context as u8 {
            return Err("H21 statement context order".into());
        }
        let terminal = take_usize(input, &mut offset, "H21 terminal conversion")?;
        let exponent = take_usize(input, &mut offset, "H21 exponent conversion")?;
        let source_tag = take(input, &mut offset, 1)?[0];
        let source_value = take_u64(input, &mut offset)?;
        let branch_tag = take(input, &mut offset, 1)?[0];
        let branch_value = take_u64(input, &mut offset)?;
        *parameter = PublicMapParameters {
            terminal,
            exponent,
            lower: LowerSelector {
                source: decode_source(source_tag, source_value)?,
                branch: decode_branch(branch_tag, branch_value)?,
            },
        };
    }
    if offset != input.len() {
        return Err("H21 statement trailing bytes".into());
    }
    let statement = H21Statement { root, total, tip, tip_time, parameters };
    validate_statement(&statement)?;
    Ok(statement)
}

fn read_u32(input: &[u8], offset: &mut usize) -> Result<u32, String> {
    let bytes: [u8; 4] = take(input, offset, 4)?.try_into()
        .map_err(|_| "H21 length extent")?;
    Ok(u32::from_le_bytes(bytes))
}

fn take_payload<'a>(input: &'a [u8], offset: &mut usize, expected: usize,
    cap: usize, label: &'static str) -> Result<&'a [u8], String> {
    let length = usize::try_from(read_u32(input, offset)?)
        .map_err(|_| "H21 payload length conversion")?;
    if length > cap || length != expected {
        return Err(label.into());
    }
    take(input, offset, length)
}

pub(super) fn decode_packet(input: &[u8]) -> Result<DecodedH21Packet, String> {
    if input.len() > MAX_PACKET_BYTES {
        return Err("H21 packet exceeds cap".into());
    }
    let mut offset = 0usize;
    if take(input, &mut offset, 8)? != PACKET_MAGIC {
        return Err("H21 packet magic".into());
    }
    if take(input, &mut offset, 4)? != [VERSION, PROFILE, 7, 0] {
        return Err("H21 packet profile".into());
    }
    if take(input, &mut offset, 1)?[0] != 0x10 {
        return Err("H21 statement field tag".into());
    }
    let statement_payload = take_payload(input, &mut offset, STATEMENT_BYTES,
        MAX_STATEMENT_BYTES, "H21 statement payload length")?;
    let statement = decode_statement(statement_payload)?;

    if take(input, &mut offset, 1)?[0] != 0x11 {
        return Err("H21 key field tag".into());
    }
    let key_payload = take_payload(input, &mut offset, KEY_BYTES, KEY_BYTES,
        "H21 key payload length")?;
    if take(input, &mut offset, 1)?[0] != 0x12 {
        return Err("H21 commitment field tag".into());
    }
    let commitment_payload = take_payload(input, &mut offset, COMMITMENT_BYTES,
        COMMITMENT_BYTES, "H21 commitment payload length")?;

    let mut role_payloads: [Vec<u8>; 7] = std::array::from_fn(|_| Vec::new());
    for index in 0..7 {
        let header = take(input, &mut offset, 5)?;
        if header[0] != 0x20 || header[1] != index as u8 ||
            header[2] != INPUT_BITS[index] || header[3] != ROW_BITS[index] || header[4] != 1 {
            return Err("H21 role header".into());
        }
        let payload = take_payload(input, &mut offset, GKR_BYTES[index], GKR_BYTES[index],
            "H21 role payload length")?;
        role_payloads[index] = payload.to_vec();
    }

    if take(input, &mut offset, 4)? != [0x30, 41, 7, 0] {
        return Err("H21 common header".into());
    }
    let common_length = usize::try_from(read_u32(input, &mut offset)?)
        .map_err(|_| "H21 common payload length conversion")?;
    if common_length == 0 || common_length > MAX_COMMON_BYTES {
        return Err("H21 common payload length".into());
    }
    let common_payload = take(input, &mut offset, common_length)?;
    if take(input, &mut offset, 1)?[0] != 0xff || offset != input.len() {
        return Err("H21 packet terminator or trailing bytes".into());
    }

    Ok(DecodedH21Packet {
        statement,
        statement_bytes: statement_payload.to_vec(),
        key: key_payload.to_vec(),
        commitment: commitment_payload.to_vec(),
        roles: role_payloads,
        common: common_payload.to_vec(),
    })
}

fn append_field(out: &mut Vec<u8>, tag: u8, payload: &[u8]) -> Result<(), String> {
    let length = u32::try_from(payload.len()).map_err(|_| "H21 field length conversion")?;
    out.push(tag);
    out.extend_from_slice(&length.to_le_bytes());
    out.extend_from_slice(payload);
    Ok(())
}

pub(super) fn encode_packet(packet: &DecodedH21Packet) -> Result<Vec<u8>, String> {
    let statement_bytes = encode_statement(&packet.statement)?;
    if packet.statement_bytes != statement_bytes {
        return Err("H21 statement bytes do not match structured statement".into());
    }
    if packet.statement_bytes.len() > MAX_STATEMENT_BYTES ||
        packet.key.len() != KEY_BYTES || packet.commitment.len() != COMMITMENT_BYTES ||
        packet.common.is_empty() || packet.common.len() > MAX_COMMON_BYTES {
        return Err("H21 packet field extent".into());
    }
    let mut total = 8usize + 4 + 1 + 4 + packet.statement_bytes.len()
        + 1 + 4 + packet.key.len() + 1 + 4 + packet.commitment.len();
    for index in 0..7 {
        if packet.roles[index].len() != GKR_BYTES[index] {
            return Err("H21 role field extent".into());
        }
        total = total.checked_add(5 + 4 + packet.roles[index].len())
            .ok_or("H21 packet size overflow")?;
    }
    total = total.checked_add(4 + 4 + packet.common.len() + 1)
        .ok_or("H21 packet size overflow")?;
    if total > MAX_PACKET_BYTES {
        return Err("H21 packet exceeds cap".into());
    }

    let mut out = Vec::with_capacity(total);
    out.extend_from_slice(PACKET_MAGIC);
    out.extend_from_slice(&[VERSION, PROFILE, 7, 0]);
    append_field(&mut out, 0x10, &packet.statement_bytes)?;
    append_field(&mut out, 0x11, &packet.key)?;
    append_field(&mut out, 0x12, &packet.commitment)?;
    for index in 0..7 {
        out.extend_from_slice(&[0x20, index as u8, INPUT_BITS[index], ROW_BITS[index], 1]);
        let role_length = u32::try_from(packet.roles[index].len())
            .map_err(|_| "H21 role length conversion")?;
        out.extend_from_slice(&role_length.to_le_bytes());
        out.extend_from_slice(&packet.roles[index]);
    }
    out.extend_from_slice(&[0x30, 41, 7, 0]);
    let common_length = u32::try_from(packet.common.len())
        .map_err(|_| "H21 common payload length conversion")?;
    out.extend_from_slice(&common_length.to_le_bytes());
    out.extend_from_slice(&packet.common);
    out.push(0xff);
    if out.len() != total {
        return Err("H21 packet encoded extent".into());
    }
    Ok(out)
}
