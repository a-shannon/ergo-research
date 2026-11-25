//! Bounded immutable input adapters for Mainnet H3 and diagnostic H4 prefixes.
//!
//! This validates canonical encoding, contiguous height/parent links, and the
//! Mainnet genesis anchor. It does not validate proof of work or difficulty.
use blake2::{Blake2b, Digest, digest::consts::U32};
use ergo_header_core::Header;
use std::{fmt, io::Read};

const MAGIC: &[u8; 4] = b"NPH2";
const HEADER_COUNT: usize = 3;
const H4_HEADER_COUNT: usize = 4;
const MAX_HEADER_BYTES: usize = 514;
const MAX_FRAME_BYTES: usize = 8 + HEADER_COUNT * (4 + MAX_HEADER_BYTES);
const MAX_H4_FRAME_BYTES: usize = 8 + H4_HEADER_COUNT * (4 + MAX_HEADER_BYTES);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Nph2Error {
    InputTooLarge,
    Truncated,
    BadMagic,
    HeaderCount,
    HeaderCount4,
    HeaderLength,
    ReadError(String),
    InvalidHeader(String),
    NonCanonicalHeader,
    WrongHeight { expected: u32, actual: u32 },
    WrongParent { height: u32 },
    WrongGenesis,
    TrailingBytes,
}

impl fmt::Display for Nph2Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InputTooLarge => write!(f, "NPH2 frame exceeds fixed size cap"),
            Self::Truncated => write!(f, "NPH2 frame is truncated"),
            Self::BadMagic => write!(f, "NPH2 magic mismatch"),
            Self::HeaderCount => write!(f, "NPH2 must contain exactly three headers"),
            Self::HeaderCount4 => write!(f, "NPH2 must contain exactly four headers"),
            Self::HeaderLength => write!(f, "NPH2 header length is outside 1..=514"),
            Self::ReadError(error) => write!(f, "could not read NPH2 frame: {error}"),
            Self::InvalidHeader(error) => write!(f, "invalid Ergo header: {error}"),
            Self::NonCanonicalHeader => write!(f, "header does not round-trip canonically"),
            Self::WrongHeight { expected, actual } =>
                write!(f, "expected header height {expected}, got {actual}"),
            Self::WrongParent { height } => write!(f, "parent link mismatch at height {height}"),
            Self::WrongGenesis => write!(f, "first header is not anchored to Mainnet genesis"),
            Self::TrailingBytes => write!(f, "NPH2 frame has trailing bytes"),
        }
    }
}

impl std::error::Error for Nph2Error {}

pub struct HeaderRecord {
    raw: Vec<u8>,
    decoded: Header,
    id: [u8; 32],
}

impl HeaderRecord {
    pub fn raw_bytes(&self) -> &[u8] { &self.raw }
    pub fn decoded(&self) -> &Header { &self.decoded }
    pub fn id(&self) -> &[u8; 32] { &self.id }
}

/// A fixed-size, validated contiguous prefix: Mainnet genesis and the following two headers.
pub struct MainnetH3Input {
    headers: [HeaderRecord; HEADER_COUNT],
}

impl MainnetH3Input {
    /// Reads at most the fixed frame cap plus one byte before rejecting an oversized input.
    pub fn read_nph2<R: std::io::Read>(reader: R) -> Result<Self, Nph2Error> {
        let bytes = read_nph2_frame(reader, MAX_FRAME_BYTES)?;
        Self::decode_nph2(&bytes)
    }

    pub fn decode_nph2(bytes: &[u8]) -> Result<Self, Nph2Error> {
        let headers = decode_nph2_prefix(bytes, HEADER_COUNT, MAX_FRAME_BYTES, Nph2Error::HeaderCount)?
            .try_into().map_err(|_| Nph2Error::HeaderCount)?;
        Ok(Self { headers })
    }

    pub fn headers(&self) -> &[HeaderRecord; HEADER_COUNT] { &self.headers }
}

/// Diagnostic-only exact Mainnet prefix: genesis and the following three headers.
/// This adapter does not define a full-history input or verify PoW/difficulty.
pub struct MainnetH4Input {
    headers: [HeaderRecord; H4_HEADER_COUNT],
}

impl MainnetH4Input {
    /// Reads at most the four-header frame cap plus one byte before rejecting oversized input.
    pub fn read_nph2<R: std::io::Read>(reader: R) -> Result<Self, Nph2Error> {
        let bytes = read_nph2_frame(reader, MAX_H4_FRAME_BYTES)?;
        Self::decode_nph2(&bytes)
    }

    pub fn decode_nph2(bytes: &[u8]) -> Result<Self, Nph2Error> {
        let headers = decode_nph2_prefix(bytes, H4_HEADER_COUNT, MAX_H4_FRAME_BYTES, Nph2Error::HeaderCount4)?
            .try_into().map_err(|_| Nph2Error::HeaderCount4)?;
        Ok(Self { headers })
    }

    pub fn headers(&self) -> &[HeaderRecord; H4_HEADER_COUNT] { &self.headers }
}

fn read_nph2_frame<R: Read>(reader: R, max_frame_bytes: usize) -> Result<Vec<u8>, Nph2Error> {
    let mut bytes = Vec::with_capacity(max_frame_bytes);
    reader.take((max_frame_bytes + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| Nph2Error::ReadError(error.to_string()))?;
    Ok(bytes)
}

fn decode_nph2_prefix(
    bytes: &[u8], expected_count: usize, max_frame_bytes: usize, count_error: Nph2Error,
) -> Result<Vec<HeaderRecord>, Nph2Error> {
    if bytes.len() > max_frame_bytes { return Err(Nph2Error::InputTooLarge); }
    if bytes.len() < 8 { return Err(Nph2Error::Truncated); }
    if &bytes[..4] != MAGIC { return Err(Nph2Error::BadMagic); }

    let mut offset = 4usize;
    let count = read_word(bytes, &mut offset)? as usize;
    if count != expected_count { return Err(count_error); }

    let mut headers: Vec<HeaderRecord> = Vec::with_capacity(expected_count);
    for index in 0..expected_count {
        let length = read_word(bytes, &mut offset)? as usize;
        if !(1..=MAX_HEADER_BYTES).contains(&length) {
            return Err(Nph2Error::HeaderLength);
        }
        let end = offset.checked_add(length).ok_or(Nph2Error::Truncated)?;
        let raw = bytes.get(offset..end).ok_or(Nph2Error::Truncated)?;
        offset = end;

        let decoded = Header::decode(raw, None)
            .map_err(|error| Nph2Error::InvalidHeader(format!("{error:?}")))?;
        let canonical = decoded.encode()
            .map_err(|error| Nph2Error::InvalidHeader(format!("{error:?}")))?;
        if canonical.as_slice() != raw { return Err(Nph2Error::NonCanonicalHeader); }

        let expected_height = index as u32 + 1;
        if decoded.height != expected_height {
            return Err(Nph2Error::WrongHeight { expected: expected_height, actual: decoded.height });
        }
        let id: [u8; 32] = Blake2b::<U32>::digest(raw).into();
        if index == 0 {
            if decoded.parent_id != [0; 32] { return Err(Nph2Error::WrongParent { height: expected_height }); }
            if id.as_slice() != crate::header_order::MAINNET_GENESIS {
                return Err(Nph2Error::WrongGenesis);
            }
        } else if decoded.parent_id.as_slice() != headers[index - 1].id.as_slice() {
            return Err(Nph2Error::WrongParent { height: expected_height });
        }
        headers.push(HeaderRecord { raw: raw.to_vec(), decoded, id });
    }
    if offset != bytes.len() { return Err(Nph2Error::TrailingBytes); }
    Ok(headers)
}

fn read_word(bytes: &[u8], offset: &mut usize) -> Result<u32, Nph2Error> {
    let end = offset.checked_add(4).ok_or(Nph2Error::Truncated)?;
    let word: [u8; 4] = bytes.get(*offset..end).ok_or(Nph2Error::Truncated)?
        .try_into().map_err(|_| Nph2Error::Truncated)?;
    *offset = end;
    Ok(u32::from_be_bytes(word))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture_prefix(count: usize) -> Vec<Vec<u8>> {
        let pack: serde_json::Value = serde_json::from_str(include_str!(
            "../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json"
        )).unwrap();
        pack["networks"]["mainnet"]["source_headers_hex"].as_array().unwrap()
            .iter().take(count).map(|item| {
                let value = item.as_str().unwrap();
                value.as_bytes().chunks_exact(2).map(|pair|
                    u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap()
                ).collect()
            }).collect()
    }

    fn fixture_headers() -> Vec<Vec<u8>> { fixture_prefix(HEADER_COUNT) }
    fn fixture_h4_headers() -> Vec<Vec<u8>> { fixture_prefix(H4_HEADER_COUNT) }

    fn frame(headers: &[Vec<u8>]) -> Vec<u8> {
        let mut out = MAGIC.to_vec();
        out.extend_from_slice(&(headers.len() as u32).to_be_bytes());
        for header in headers {
            out.extend_from_slice(&(header.len() as u32).to_be_bytes());
            out.extend_from_slice(header);
        }
        out
    }

    #[test]
    fn accepts_exact_canonical_mainnet_h3_prefix() {
        let input = MainnetH3Input::decode_nph2(&frame(&fixture_headers())).unwrap();
        assert_eq!(input.headers().len(), HEADER_COUNT);
        for (index, header) in input.headers().iter().enumerate() {
            assert_eq!(header.decoded().height, index as u32 + 1);
            assert_eq!(header.decoded().encode().unwrap(), header.raw_bytes());
            assert_eq!(Blake2b::<U32>::digest(header.raw_bytes()).as_slice(), header.id());
        }
    }

    #[test]
    fn rejects_bad_magic_count_lengths_truncation_and_trailing_bytes() {
        let headers = fixture_headers();
        let valid = frame(&headers);

        let mut bad = valid.clone(); bad[0] ^= 1;
        assert!(matches!(MainnetH3Input::decode_nph2(&bad), Err(Nph2Error::BadMagic)));
        assert!(matches!(MainnetH3Input::decode_nph2(&frame(&headers[..2])), Err(Nph2Error::HeaderCount)));
        let mut bad = valid.clone(); bad[8..12].copy_from_slice(&0u32.to_be_bytes());
        assert!(matches!(MainnetH3Input::decode_nph2(&bad), Err(Nph2Error::HeaderLength)));
        let mut bad = valid.clone(); bad[8..12].copy_from_slice(&515u32.to_be_bytes());
        assert!(matches!(MainnetH3Input::decode_nph2(&bad), Err(Nph2Error::HeaderLength)));
        assert!(matches!(MainnetH3Input::decode_nph2(&valid[..valid.len()-1]), Err(Nph2Error::Truncated)));
        let mut bad = valid; bad.push(0);
        assert!(matches!(MainnetH3Input::decode_nph2(&bad), Err(Nph2Error::TrailingBytes)));
        assert!(matches!(MainnetH3Input::decode_nph2(&[b'N',b'P']), Err(Nph2Error::Truncated)));
    }

    #[test]
    fn rejects_invalid_header_height_parent_and_genesis_anchor() {
        let mut headers = fixture_headers();
        headers[1] = {
            let mut header = Header::decode(&headers[1], None).unwrap();
            header.height = 9;
            header.encode().unwrap()
        };
        assert!(matches!(MainnetH3Input::decode_nph2(&frame(&headers)), Err(Nph2Error::WrongHeight { expected: 2, actual: 9 })));

        let mut headers = fixture_headers();
        headers[1] = {
            let mut header = Header::decode(&headers[1], None).unwrap();
            header.parent_id = [0; 32];
            header.encode().unwrap()
        };
        assert!(matches!(MainnetH3Input::decode_nph2(&frame(&headers)), Err(Nph2Error::WrongParent { height: 2 })));

        let mut headers = fixture_headers();
        headers[0] = {
            let mut header = Header::decode(&headers[0], None).unwrap();
            header.timestamp += 1;
            header.encode().unwrap()
        };
        assert!(matches!(MainnetH3Input::decode_nph2(&frame(&headers)), Err(Nph2Error::WrongGenesis)));
    }

    #[test]
    fn rejects_invalid_header_bytes_and_oversized_frame() {
        assert!(matches!(MainnetH3Input::decode_nph2(&frame(&[vec![0], vec![0], vec![0]])),
            Err(Nph2Error::InvalidHeader(_))));
        assert!(matches!(MainnetH3Input::decode_nph2(&vec![0; MAX_FRAME_BYTES + 1]),
            Err(Nph2Error::InputTooLarge)));
        assert!(matches!(MainnetH3Input::read_nph2(std::io::Cursor::new(vec![0; MAX_FRAME_BYTES + 100])),
            Err(Nph2Error::InputTooLarge)));
    }

    #[test]
    fn accepts_exact_canonical_mainnet_h4_diagnostic_prefix() {
        let fixture = fixture_h4_headers();
        let input = MainnetH4Input::decode_nph2(&frame(&fixture)).unwrap();
        assert_eq!(input.headers().len(), H4_HEADER_COUNT);
        for (index, header) in input.headers().iter().enumerate() {
            assert_eq!(header.decoded().height, index as u32 + 1);
            assert_eq!(header.decoded().encode().unwrap(), header.raw_bytes());
            assert_eq!(Blake2b::<U32>::digest(header.raw_bytes()).as_slice(), header.id());
            if index == 0 {
                assert_eq!(header.decoded().parent_id, [0; 32]);
                assert_eq!(header.id().as_slice(), crate::header_order::MAINNET_GENESIS);
            } else {
                assert_eq!(header.decoded().parent_id.as_slice(), input.headers()[index - 1].id().as_slice());
            }
        }
        let from_reader = MainnetH4Input::read_nph2(std::io::Cursor::new(frame(&fixture))).unwrap();
        assert_eq!(from_reader.headers()[3].raw_bytes(), input.headers()[3].raw_bytes());
    }

    #[test]
    fn rejects_h4_count_size_truncation_and_trailing_bytes() {
        let headers = fixture_h4_headers();
        let valid = frame(&headers);
        assert!(matches!(MainnetH4Input::decode_nph2(&frame(&headers[..3])), Err(Nph2Error::HeaderCount4)));
        let mut five = headers.clone(); five.push(headers[3].clone());
        assert!(matches!(MainnetH4Input::decode_nph2(&frame(&five)), Err(Nph2Error::HeaderCount4)));

        let mut bad_length = valid.clone(); bad_length[8..12].copy_from_slice(&0u32.to_be_bytes());
        assert!(matches!(MainnetH4Input::decode_nph2(&bad_length), Err(Nph2Error::HeaderLength)));
        let mut bad_length = valid.clone(); bad_length[8..12].copy_from_slice(&515u32.to_be_bytes());
        assert!(matches!(MainnetH4Input::decode_nph2(&bad_length), Err(Nph2Error::HeaderLength)));
        assert!(matches!(MainnetH4Input::decode_nph2(&valid[..valid.len()-1]), Err(Nph2Error::Truncated)));
        assert!(matches!(MainnetH4Input::decode_nph2(&[b'N',b'P']), Err(Nph2Error::Truncated)));
        let mut trailing = valid.clone(); trailing.push(0);
        assert!(matches!(MainnetH4Input::decode_nph2(&trailing), Err(Nph2Error::TrailingBytes)));
        assert!(matches!(MainnetH4Input::decode_nph2(&vec![0; MAX_H4_FRAME_BYTES + 1]),
            Err(Nph2Error::InputTooLarge)));
        assert!(matches!(MainnetH4Input::read_nph2(std::io::Cursor::new(vec![0; MAX_H4_FRAME_BYTES + 100])),
            Err(Nph2Error::InputTooLarge)));
    }

    #[test]
    fn h4_checks_genesis_height_and_every_parent_edge() {
        let mut bad_genesis_parent = fixture_h4_headers();
        bad_genesis_parent[0] = {
            let mut header = Header::decode(&bad_genesis_parent[0], None).unwrap();
            header.parent_id = [1; 32];
            header.encode().unwrap()
        };
        assert!(matches!(MainnetH4Input::decode_nph2(&frame(&bad_genesis_parent)),
            Err(Nph2Error::WrongParent { height: 1 })));

        for index in 1..H4_HEADER_COUNT {
            let mut bad_parent = fixture_h4_headers();
            bad_parent[index] = {
                let mut header = Header::decode(&bad_parent[index], None).unwrap();
                header.parent_id = [0; 32];
                header.encode().unwrap()
            };
            assert!(matches!(MainnetH4Input::decode_nph2(&frame(&bad_parent)),
                Err(Nph2Error::WrongParent { height }) if height == index as u32 + 1),
                "must check H4 chain edge ending at height {}", index + 1);
        }

        let mut bad_height = fixture_h4_headers();
        bad_height[3] = {
            let mut header = Header::decode(&bad_height[3], None).unwrap();
            header.height = 5;
            header.encode().unwrap()
        };
        assert!(matches!(MainnetH4Input::decode_nph2(&frame(&bad_height)),
            Err(Nph2Error::WrongHeight { expected: 4, actual: 5 })));

        let mut bad_genesis = fixture_h4_headers();
        bad_genesis[0] = {
            let mut header = Header::decode(&bad_genesis[0], None).unwrap();
            header.timestamp += 1;
            header.encode().unwrap()
        };
        assert!(matches!(MainnetH4Input::decode_nph2(&frame(&bad_genesis)), Err(Nph2Error::WrongGenesis)));
    }
}
