# Work-coordinate audit candidate AUD01

Working draft 0.9-r4, sections 2–4, fixes the inputs, sample distribution and acceptance rule. AUD01 proposes the byte framing for a local implementation. A certificate profile selecting AUD01 must bind this framing, SHA-512, the number of samples, the unchanged work-tree codec and the structural verifier.

A verifier obtains all inputs from the same successfully verified full structural object. Its canonical statement `x` covers the requested profile and query. Its complete structural argument `pi_s` includes any anchor openings used to authenticate statement fields. Work `W`, following work `F`, terminal height `n` and tree root come from that object. The public audit response is a separate frame.

## Challenge bytes

Concatenate the rows in this table, then compute SHA-512 over the resulting bytes. Read its 64 output bytes as an unsigned big-endian integer. All integer fields have fixed width.

| Field | Encoding |
|---|---|
| Domain | ASCII `Ergo-NiPoPoW-V2/audit/r4/1` followed by one zero byte |
| Statement | U64BE byte length followed by every byte of `x` |
| Structural argument | U64BE byte length followed by every byte of `pi_s` |
| Scale | U224BE work length |
| Draw index | U32BE, 0 through 465 |
| Attempt | U32BE, 1 or 2 |

Require `0 < F <= W`. Start at `F` and double until the next scale reaches or exceeds `W`. Use `W` exactly once. At every scale `ell`, take the first attempt with integer value `X < 2^512 - (2^512 mod ell)` and emit `W - ell + (X mod ell)`. Two rejected attempts abort the entire audit. Keep all 466 draws per scale, including repeats. The implementation clones the unfinished SHA-512 state after processing the common bytes.

For an independent test vector set `x = 7879` and `pi_s = 7a` in hexadecimal, `W = 10`, `F = 3`. The first coordinates of scales 3, 6 and 10 are respectively 8, 6 and 6. Encode all 1,398 coordinates as U224BE in generation order and concatenate them. Their SHA-256 is `e7ef8584f80b5a3456e30a3215d35ce8a41f3021ed652e7d74dd6e7c682d07d5`.

## Opening bytes

An audit response starts with the eight ASCII bytes `AUDOPEN1` and a U32BE count. Each entry is a U16BE length followed by one canonical `NIPOWP01` opening. Entries occur in strictly increasing authenticated leaf position. Include exactly one entry per distinct sampled header, with its existing tree path. A single entry may cover many draws.

The consumer sorts the draws. It verifies each opening against the authenticated root, count and total at the first outstanding coordinate, then checks native Autolykos on the header returned by that membership operation. Every remaining draw below that interval's exclusive upper bound shares the checked header. Admission requires consuming all draws and exactly all input bytes. The parser bounds every entry by the existing work-opening limit and bounds the entry count by the number of draws.

`native_audit.rs` supplies the producer and consumer as a child module of the full structural verifier. The producer looks up intervals in the retained tree and emits openings. The verifier requires only the verified structural object and the response bytes. Its accepted result borrows the verified object.
