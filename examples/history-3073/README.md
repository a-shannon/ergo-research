# Structural prefix and authenticated header openings

This example contains a deterministic structural proof for the Ergo mainnet prefix from genesis through height 3073. Seven GKR role proofs and one common PCS opening are verified against one original log32 witness commitment. The roles cover canonical header/BLAKE constraints, the work tree, height/work/difficulty relations including the retarget at 3073, parent links, point membership and metadata ordering.

The verified result issues an opaque history handle. Openings for headers 1024, 2048 and 3072 are checked under the root and work total carried by that handle. A caller-selected root cannot issue the same certification.

The `public/` directory contains ten files totaling 95,736 bytes. `key.bin` is 33,264 bytes; `key-metadata.bin` is 40 bytes. These select the diagnostic key policy. Each of the three work-tree openings is 733 bytes. The 512 MiB producer witness is absent. A separate public RAW prefix is included with the [checkpoint example](../checkpoint-1024-1087/README.md) solely for reproducing its export.

First follow the build and external-data staging instructions in the [main README](../../README.md). From the checkout root, with `$history` pointing to the staged copy outside the source directory:

```powershell
Get-ChildItem Env: | Where-Object Name -like 'NIPOPOW_*' |
    ForEach-Object { Remove-Item -LiteralPath ('Env:' + $_.Name) }
$env:NIPOPOW_COMMON51_PUBLIC_DIR = Join-Path $history 'public'
$env:NIPOPOW_COMMON51_KEY_PATH = Join-Path $history 'key.bin'
$env:NIPOPOW_COMMON51_KEY_METADATA_PATH = Join-Path $history 'key-metadata.bin'
$env:NIPOPOW_C584_OPENING_DIR = Join-Path $history 'openings'
cargo test --lib --locked historical_prefix_proof::historical_verified_work_tests::c584_verified_history_opening_cold_consumer -- --ignored --exact --test-threads=1 --nocapture
if ($LASTEXITCODE -ne 0) { throw 'Structural membership check failed' }
```

To verify native Autolykos on the same three authenticated headers, keep these inputs and run:

```powershell
cargo test --lib --locked historical_prefix_proof::historical_verified_work_tests::c585_history_bound_native_pow_cold_consumer -- --ignored --exact --test-threads=1 --nocapture
if ($LASTEXITCODE -ne 0) { throw 'History-bound PoW check failed' }
```

This consumer verifies the structural packet once, authenticates each opened header, then consumes that member in the native PoW verifier. The result retains the same verified-history identity. The three-header membership/PoW phase took about two milliseconds locally; the complete fresh process, including structural verification and nine clone-predicate rejection controls, took about six seconds at peak Job memory 1.08 GB with four Rayon workers.

The key is TESTONLY and the cryptographic construction remains experimental. These are three fixed v1 headers. They do not implement proof-derived sampling, historical v2 coverage, current-tip selection, freshness, chain comparison or complete NiPoPoW V2 security. The timings do not estimate full-chain synchronization.
