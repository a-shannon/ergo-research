# Four-header proof packet

This example contains an exported proof for the canonical hashes, parent links and fixed heights of four consecutive Ergo mainnet headers at heights 3072–3075. It also proves decoded-difficulty carry from 3073 to 3074, for positive difficulty bounded by the profile's q. Different compact encodings of the same difficulty are supported. The producer uses one committed witness, one GKR argument, and one PCS opening. The verifier reads only `expected.json` and `packet.bin`; the producer's 524,288-byte `witness.bits` is absent from this directory.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `expected.json` | 1,682 | `583923C6BDABE67734BB48FE7DF26CF78E35351D53CA384ADD0D7A2987F0C839` |
| `packet.bin` | 34,501 | `B538E8CD29B4F24EBDB0BC047A3AEF95BC4A1D5541A50C5AA79A8392A74B6854` |

From the repository root, set `NIPOPOW_FOUR_LINK_PACKET_INPUT_DIR` to the absolute path of this directory. Then run:

```sh
cargo test --lib --locked four_header_link_packet::integration_tests::four_header_packet_fresh_serialized_consumer -- --ignored --exact --test-threads=1 --nocapture
```

To regenerate the packet, set `NIPOPOW_FOUR_LINK_PACKET_DIR` to a fresh empty directory outside the source tree and run:

```sh
cargo test --lib --locked four_header_link_packet::integration_tests::four_header_packet_producer_one_gkr_one_pcs_exports_and_faults -- --exact --test-threads=1 --nocapture
```

The local producer completed in 33.3 seconds with a 1.53 GB peak Job memory. A separate cold process accepted the packet in 7.4 seconds with a 1.23 GB peak; its positive cryptographic verification took about 0.85 seconds. The complete consumer run also exercises malformed-statement, endpoint, packet-decoder and cryptographic rejection cases. These measurements use one Rayon thread on the local development machine.

The packet is larger than four raw headers. This experiment tests one real-data proof export and cold verification path with a single DAA carry relation; it does not establish useful compression at four headers, the retarget at 3073, other DAA transitions, proof of work, cumulative-work validity, full-history security, or production parameters. The backend uses diagnostic BN254 settings. Its v2 statement and proof domain reject the earlier link-only v1 profile.
