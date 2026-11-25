# Historical proof review

The producer regenerated all seven GKR arguments and their common Dory opening for the first 3,073 Ergo mainnet headers. All ten public files are byte-for-byte identical to the r6 historical example. This release adds the public headers and a source bundle to verify that packet or reproduce its opening, together with two role-0 checkpoints on much longer histories.

## Verify the 3,073-header packet

Download [the historical opening review kit](https://github.com/a-shannon/ergo-research/releases/download/nipopow-v2-historical-review-r7/ergo-nipopow-v2-historical-opening-3073-review.zip). Extract it, open a PowerShell prompt in its root, and run this command on 64-bit Windows with Python 3.12 and Rust (MSVC linker and Windows SDK installed).

```powershell
python -I -B ./accelerated-producer/producer.py verify-historical-opening N1 --case ./examples/history-3073 --kit ./era-bound-verifier-kit --work ../nipopow-r7-work
```

The first invocation builds the receiver. Success ends with `Verified the preview r6 seven-role opening on 3,073 historical headers.` The receiver derives seven evaluation claims and checks one opening against the public commitment. It uses only the ten public packet files plus the log32 key and key metadata. The command's `N1` argument selects the build profile for this historical fixture.

The packet totals 95,736 bytes, including a 45,501-byte opening. Its SHA-256 is `a7c1d3d3e153b155a79e97cb6cda7437261ecdf2d6ebcf318f081029f9f966ac` for the opening alone. The kit README gives the optional steps to rebuild the 512 MiB witness from the included headers, reproduce the opening from the supplied arguments and archived sumcheck messages, and run the receiver on that new export.

## Measured generation and verification

In a separate production experiment, the prover started from the retained 512 MiB witness, generated all seven arguments and the common opening, and copied the public packet to a fresh receiver directory. It used a GPU for sixteen rounds of one relation and a memory optimization for another. Active time through export was **4 h 39 min 12 s**. The separate CPU receiver accepted the copied bytes in **9.98 s**. These timings exclude compilation, witness preparation and the scheduling pause between producer stages. The OS page cache was uncontrolled. They cover the legacy PoW era at height 3,073 under a diagnostic BN254/log32 key. Full-history AUD2 issuance, renewal and light-client synchronization remain to be measured.

## Full-history work in progress

[Download the two role-0 checkpoints](https://github.com/a-shannon/ergo-research/releases/download/nipopow-v2-historical-review-r7/ergo-nipopow-v2-role0-checkpoints.zip) to inspect the first GKR argument, statement and commitment for each experimental log41 snapshot. The respective producers checked and saved the two 9,280-byte arguments. The bundle includes the shared public key and SHA-256 values. Each full certificate still requires all seven relations, one common opening, the native work audit and the continuation.

| Snapshot | Header count | Maturity height | Role-0 SHA-256 |
| --- | ---: | ---: | --- |
| N0 | 1,819,648 | 1,804,171 | `9011c767940721ec311c197be76e14e4edcfa2a53e1cc2882a0b076a206b1703` |
| N1 | 1,827,840 | 1,810,842 | `2df8c1040df00f3a70bc59a598bb7bb49735351a6833cbe61473430e7606bf31` |

## Download integrity

| File | SHA-256 |
| --- | --- |
| `ergo-nipopow-v2-historical-opening-3073-review.zip` | `8ca7ea40c83be294c239fd8c287e3143b2dcd8578dc551e9fdd1890fd97576f4` |
| `ergo-nipopow-v2-role0-checkpoints.zip` | `cfa697e9b794679118258d9a143be47b41ea4654be908361efb3fb3ce61e220e` |
