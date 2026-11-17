# Developer preview status

This preview lets a reviewer rebuild a checkpoint packet for the Ergo mainnet prefix ending at height 3073, then verify the exported packet in a separate process. It includes the source, public proof inputs and the small RAW prefix needed for that export. The producer's 512 MiB structural witness is not included.

The final target is a compact certificate from genesis to a recent tip, verified with four CPU cores, 8 GiB of memory and no GPU. The following results establish bounded components of that construction.

| Requirement | Source and applicability | Evidence in this preview | Remaining work and owner |
| --- | --- | --- | --- |
| Reproducible developer preview | Preview interface contract; applies to this package | Locked source and public examples rebuilt from an extracted archive; included packet, new export and independent receiver all passed | Verified locally on Windows x64; CI not run |
| Canonical history, difficulty and exact cumulative work | Ergo consensus reference and draft 0.9; final certificate | Seven GKR roles and one common PCS opening accepted for the retained genesis-to-3073 prefix | Generalized full-history producer: implementation |
| Authenticated checkpoint and following work | Checkpoint interface; bounded diagnostic | Two structural Merkle openings under the same verified history bind heights 1024 and 1087; the verifier derives following work by exact subtraction | Complete profile S and maturity guards: implementation and security review |
| Producer to exported proof to independent receiver | Required preview boundary | Real role0 production from the retained 512 MiB witness reproduces the retained proof; a separate consumer accepts the complete bounded packet | Verified for N3073; one optimized run was 3.99% faster, without a full-history forecast |
| Native proof of work on authenticated headers | Draft 0.9 audit component | Three fixed v1 headers at heights 1024, 2048 and 3072 pass membership and native Autolykos; v1/v2 predicates have component fixtures | Proof-derived work-weighted sampler and historical v2 integration: implementation |
| Full-history witness and proof | Final target | Full-history native row construction and selected constraint differentials exist | Complete source, prover admission, common commitment and resource qualification: implementation |
| Recent-tip selection and continuation | Draft 0.9 final certificate | No complete client result in this preview | Full S, chain comparison, continuation and freshness: implementation |
| Cryptographic production qualification | Final security requirement | Experimental GKR–Dory/BN254, fixed TESTONLY diagnostic key | Production groups/key, concrete security margins and independent cryptographic qualification: research and review |
| Existing Ergo compatibility | Required throughout | Off-chain construction using existing block formats and native PoW | No hard fork or EIP-0045 dependency introduced |
| Release, licensing and maintainer acceptance | Delivery conventions | Technical-review source package; third-party notices retained | Project-authored license terms are unspecified; ordinary client API, CI, release qualification and maintainer acceptance remain open |

## Checkpoint packet

The included packet is 131,155 bytes, SHA-256 `189C8BBCB0E2F2EC996FB725A64B4D1896CDBAED94216C589481153EE2476249`. Its producer verifies the retained structural proof, reuses the existing opening for height 1024 and creates an opening for height 1087. It does not generate a new GKR argument, PCS opening or witness commitment.

A separate receiver reads only this packet. It verifies the embedded base proof and key policy, authenticates both checkpoint openings and computes following work as `24,293,759,260,819,456 - 1,303,189,546,598,400 = 22,990,569,714,221,056`. Fifteen negative controls cover the profile, claims, paths, framing and altered base proof. The verified result is a checkpoint diagnostic; it does not satisfy the complete profile, work-maturity or proof-derived audit requirements.

After a fresh archive extraction and rebuild, the included checkpoint packet passed in 9.859 seconds at peak Job memory 1,119,068,160 bytes. The packaged producer exported a new byte-identical packet in 6.334 seconds at 1,079,648,256 bytes. A separate packet-only receiver accepted that export in 9.879 seconds at 1,120,919,552 bytes. Both cold processes ran 15 rejection controls and read no RAW prefix. All stages used four Rayon workers, a 2 GiB memory cap and a 120-second wall limit. The host had more than four cores; these are bounded component measurements, not four-core light-client synchronization measurements.

## Source and validation

The computational source and fixture manifest is [SOURCE-MANIFEST.tsv](SOURCE-MANIFEST.tsv), 379 files totaling 15,333,189 bytes. Its SHA-256 is `C719D24ECB8E51BFE9ACAE8F478641BD94627833A8F6D588F1BA69092ABA240F`. It excludes documentation and example packets. The final archive digest separately identifies the complete distribution.

Rust 1.97.1 rebuilt the extracted source in the test profile with optimization level 1, assertions and overflow checks enabled. The retained test executable is 91,602,944 bytes. The compiler Job took 424.568 seconds and peaked at 6.518 GB; the root compiler exited successfully and its remaining owned process was cleaned up. Six focused tests passed on this new executable, with two fixture-dependent tests ignored. Five candidate parity tests and five unchanged checked-path tests had already passed on the identical computational source. They include non-Boolean input rejection and equality of proof bytes, claims and transcript continuation with the generic calculation.

The earlier role0 producer, using the same 512 MiB witness, key, protocol and four Rayon workers, exported its 7,264-byte proof in 1,067.269 seconds. The Boolean first-round specialization completed in 1,024.730 seconds, saving 42.539 seconds (3.99%) in this single-fixture, single-run comparison. Its bytes matched the retained role0 argument exactly, allowing reuse of the common PCS opening. A fresh process accepted all seven role arguments and that common opening in 6.361 seconds. This is one newly generated role argument, not seven newly generated arguments or a new PCS proof. The small observed gain is not a full-history throughput estimate.

The fixed-header native-PoW consumer separately accepted the structural certificate and three authenticated v1 headers in about six seconds. Its positive membership/PoW phase took about two milliseconds. The whole test includes nine detached-header predicate negatives; those controls do not mutate an opaque authenticated member.

No complete mainnet-history proof, target-device synchronization benchmark or CI result is claimed. The experimental history interface is currently available through tests, and the packaged commands are validated on Windows x64 only. See [THIRD_PARTY.md](../THIRD_PARTY.md) for component provenance and licensing status.
