# Ergo NiPoPoW V2 developer preview

NiPoPoW V2 is a proposed off-chain certificate for an Ergo header history rooted at genesis. An archival prover would commit to the header transcript and prove its structure and work; a light client would check proof-derived samples with Ergo's native Autolykos rules, then compare histories and check a recent continuation. The design uses existing blocks and mining rules. It requires no hard fork or EIP-0045.

This preview contains a Rust prototype and bounded demonstrations. It does not produce or verify a certificate for the complete mainnet history.

## Start with the checkpoint packet

The first example is [the checkpoint at heights 1024 and 1087](examples/checkpoint-1024-1087/README.md). The included 131,155-byte packet binds an authenticated header at height 1024 to a checkpoint at 1087. It also authenticates `F = W_N - W_f`: work following height 1087 through the certified tip at 3073, using the opening at 1087 and the certified total. A cold consumer verifies the packet from that file alone. It does not read the producer's NP37 prefix or a witness.

The checkpoint reuses a retained proof for the genesis-through-3073 prefix. It does not create new GKR proofs or a new PCS opening. The key is diagnostic and test-only. The packet's proof format and interface are experimental.

For the checkout and packet here, set up an isolated data directory and Cargo target from PowerShell at the repository root. The copies keep all runtime inputs and outputs outside the source tree.

```powershell
$source = (Resolve-Path '.').Path
$id = [guid]::NewGuid().ToString('N')
$work = Join-Path $env:LOCALAPPDATA ("NiPoPoW\preview-" + $id)
$data = Join-Path $work 'data'
$history = Join-Path $data 'history-3073'
$checkpoint = Join-Path $data 'checkpoint-1024-1087'
$outputs = Join-Path $work 'outputs'
$target = Join-Path $env:LOCALAPPDATA ("NiPoPoW\target-" + $id)
New-Item -ItemType Directory -Force -Path $history, $checkpoint, $outputs, $target | Out-Null
Copy-Item -Path (Join-Path $source 'examples\history-3073\*') -Destination $history -Recurse
Copy-Item -Path (Join-Path $source 'examples\checkpoint-1024-1087\*') -Destination $checkpoint -Recurse

$env:CARGO_TARGET_DIR = $target
$env:CARGO_PROFILE_TEST_OPT_LEVEL = '1'
$env:CARGO_PROFILE_TEST_DEBUG = '0'
$env:CARGO_PROFILE_TEST_DEBUG_ASSERTIONS = 'true'
$env:CARGO_PROFILE_TEST_OVERFLOW_CHECKS = 'true'
$env:CARGO_BUILD_JOBS = '2'
$env:CARGO_INCREMENTAL = '0'
$env:RAYON_NUM_THREADS = '4'
$env:RUST_MIN_STACK = '67108864'

cargo test --lib --no-run --locked
if ($LASTEXITCODE -ne 0) { throw 'Cargo compile failed' }
```

The first build may need to download locked crates. Rust 1.97.1 was used for the retained local C590 build. Clear inherited `NIPOPOW_*` variables before running the focused tests:

```powershell
Get-ChildItem Env: | Where-Object Name -Like 'NIPOPOW_*' | ForEach-Object { Remove-Item "Env:$($_.Name)" }
cargo test --lib --locked c590_ -- --test-threads=1
if ($LASTEXITCODE -ne 0) { throw 'C590 focused tests failed' }
```

Now verify the packet included with this preview. This consumer accepts only `NIPOPOW_C590_PACKET_PATH`; the packet carries the public proof and diagnostic verification inputs it needs.

```powershell
$env:NIPOPOW_C590_PACKET_PATH = (Join-Path $checkpoint 'checkpoint-1024-1087.bin')
cargo test --lib --locked historical_prefix_proof::historical_verified_work_tests::c590_checkpoint_anchor_packet_cold_consumer -- --ignored --exact --test-threads=1 --nocapture
if ($LASTEXITCODE -ne 0) { throw 'Included checkpoint packet verification failed' }
```

To reproduce the export as well, the producer needs the public genesis-through-3073 inputs, the retained NP37 prefix and the opening at height 1024. It writes a new packet outside the checkout:

```powershell
Get-ChildItem Env: | Where-Object Name -Like 'NIPOPOW_*' | ForEach-Object { Remove-Item "Env:$($_.Name)" }
$env:NIPOPOW_COMMON51_PUBLIC_DIR = Join-Path $history 'public'
$env:NIPOPOW_COMMON51_KEY_PATH = Join-Path $history 'key.bin'
$env:NIPOPOW_COMMON51_KEY_METADATA_PATH = Join-Path $history 'key-metadata.bin'
$env:NIPOPOW_C584_PREFIX_PATH = Join-Path $checkpoint 'prefix-3073.np37'
$env:NIPOPOW_C584_OPENING_DIR = Join-Path $history 'openings'
$env:NIPOPOW_C590_PACKET_OUT = Join-Path $outputs 'checkpoint-1024-1087-reproduced.bin'
cargo test --lib --locked historical_prefix_proof::historical_verified_work_tests::c590_checkpoint_anchor_packet_producer -- --ignored --exact --test-threads=1 --nocapture
if ($LASTEXITCODE -ne 0) { throw 'Checkpoint packet production failed' }
```

The producer checks that the retained prefix matches the verified base, reuses the existing seven GKR roles and common PCS, constructs the opening at 1087, and exports the checkpoint packet. It does not regenerate the base proofs. Verify the new output in a fresh process after clearing every `NIPOPOW_*` variable:

```powershell
Get-ChildItem Env: | Where-Object Name -Like 'NIPOPOW_*' | ForEach-Object { Remove-Item "Env:$($_.Name)" }
$env:NIPOPOW_C590_PACKET_PATH = Join-Path $outputs 'checkpoint-1024-1087-reproduced.bin'
cargo test --lib --locked historical_prefix_proof::historical_verified_work_tests::c590_checkpoint_anchor_packet_cold_consumer -- --ignored --exact --test-threads=1 --nocapture
if ($LASTEXITCODE -ne 0) { throw 'Reproduced checkpoint packet verification failed' }
```

The included packet is 131,155 bytes, SHA-256 `189C8BBCB0E2F2EC996FB725A64B4D1896CDBAED94216C589481153EE2476249`. A fresh extraction of this source and its examples was rebuilt and replayed: the included packet verified in 9.859 seconds, the producer exported an identical packet in 6.334 seconds, and a separate process verified that new export in 9.879 seconds. Each cold consumer also ran 15 rejection controls. The runs used four Rayon workers on a 16-core machine, with peak Job memory at most 1.121 GB under a 2 GiB cap. They are bounded component measurements, not four-core or full-chain synchronization measurements. [STATUS.md](docs/STATUS.md) records the producer measurement and the remaining release requirements.

## Other examples

- [Genesis-to-3073 proof and authenticated openings](examples/history-3073/README.md) describes the bounded structural proof and fixed-header PoW example.
- [Four-header proof packet](examples/four-header/README.md) isolates hashes, links and one decoded-difficulty carry across four mainnet headers.

## Scope and release terms

The checkpoint and structural-prefix examples use a fixed N=3073 diagnostic profile and test-only key. They do not implement the paper's complete proof-derived sampler, full-S construction, freshness checks, current-tip coverage, history comparison, safe continuation, or a full NiPoPoW V2 certificate. The four-header example has its own smaller scope. The construction has not completed its production security or parameter review. This code is for technical review.

The `THIRD_PARTY.md` file identifies the vendored Dory licenses. The license for the project-authored implementation and `vendor/header-core` is unspecified, so this preview makes no open-source reuse claim.
