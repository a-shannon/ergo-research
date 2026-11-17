# Checkpoint packet for heights 1024 and 1087

This example carries an authenticated checkpoint from the verified genesis-through-3073 history. It binds the header at height 1024 and the checkpoint at 1087. It also authenticates `F = W_N - W_f`, the work following height 1087 through the certified tip at 3073, using the authenticated opening at 1087 and the certified total work. The packet is self-contained for cold verification.

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `checkpoint-1024-1087.bin` | 131,155 | `189C8BBCB0E2F2EC996FB725A64B4D1896CDBAED94216C589481153EE2476249` |
| `prefix-3073.np37` | 869,457 | `A577D3CDE3CB063B4C4945F95C67B07FCE500486ACBD36F77AA3D3F586CB022A` |

The checkpoint packet includes the retained public proof and diagnostic key material. The cold consumer reads the packet alone; it does not read `prefix-3073.np37`, a RAW history file, or the producer's witness. The NP37 prefix is included for the optional producer reproduction below.

## Verify the included packet

From the repository root, follow the setup and test-profile commands in the [main README](../../README.md). Clear inherited `NIPOPOW_*` variables, set the path to the copied example data directory, then run the cold consumer:

```powershell
Get-ChildItem Env: | Where-Object Name -Like 'NIPOPOW_*' | ForEach-Object { Remove-Item "Env:$($_.Name)" }
$env:NIPOPOW_C590_PACKET_PATH = Join-Path $checkpoint 'checkpoint-1024-1087.bin'
cargo test --lib --locked historical_prefix_proof::historical_verified_work_tests::c590_checkpoint_anchor_packet_cold_consumer -- --ignored --exact --test-threads=1 --nocapture
if ($LASTEXITCODE -ne 0) { throw 'Checkpoint packet verification failed' }
```

The packet verifier checks the embedded base proofs and checkpoint openings, then runs its rejection controls. The consumer does not generate GKR proofs or PCS openings.

## Reproduce the packet export

The producer uses the copied [history-3073 public inputs](../history-3073/README.md), `prefix-3073.np37`, and the retained opening for height 1024. The commands in the [main README](../../README.md) set these paths, write a new packet under the isolated work directory, clear the producer environment, and verify the new packet in a separate process.

The producer reuses the seven retained GKR roles and the common PCS. It constructs the opening for height 1087 and exports a checkpoint capsule; it does not create a new base proof or PCS.

This is a fixed diagnostic example. It does not establish full-history proof generation, the paper's work-weighted sampling policy, freshness, current-tip coverage, history comparison, continuation, production parameters, or complete NiPoPoW V2 security.
