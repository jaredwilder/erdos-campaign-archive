# Running the verifiers

Every verifier published across these repositories was re-run from committed source on
2026-09-10/11, hours after the release was made public. This file records what happened, including
the two that a reader could not have invoked from the documentation as written.

## Result: 14 of 14 run green

| verifier | repository | exit | seconds |
|---|---|---|---|
| `computational/verify_finite_examples.py` | erdos-attack-logs | 0 | 0.1 |
| `computational/verify_kummer_cut_gap_bounds.py` | erdos-attack-logs | 0 | 0.1 |
| `erdos950-.../verify_nested_pattern.py` | erdos-attack-logs | 0 | 0.1 |
| `verification/verify_finite_examples.py` | eg203 | 0 | 0.1 |
| `eg203-lean/verification/lane0_verify.py` | eg203-eg411-corpus | 0 | 36.5 |
| `eg203-lean/verification/lane1_verify.py` | eg203-eg411-corpus | 0 | 3.7 |
| `eg203-lean/verification/lane4_verify.py` | eg203-eg411-corpus | 0 | 5.1 |
| `erdos28-close/verify_finite_claims.py` | erdos-campaign-archive | 0 | 2.5 |
| `erdos40-close/verify_finite_claims.py` | erdos-campaign-archive | 0 | 2.2 |
| `erdos66-close/verify_finite_identity.py` | erdos-campaign-archive | 0 | 2.3 |
| `erdos30-close/compute/verify_bounds.py` | erdos-campaign-archive | 0 | 35.9 |
| `erdos564-close/sat/verify_witness.py` | erdos-campaign-archive | 0 | 0.1 | 
| `srg-conway99/.../independent_check.py` | erdos-campaign-archive | 0 | 0.1 |
| `subagent-tau/classification_check.py` | erdos595-barrier-tower | 0 | 14.1 |

Plus, run separately and recorded in their own repositories: the Sidon `f(7) >= 24` verifier
(exit 0, 300 pairs, 300 distinct sums), the Erdos 902 `f(4) >= 49` verifier (exit 0, verdict PASS),
the C(13,6,3) cover verifier across four receipts, and a full re-run of the integral-octagon sweep
that reproduced its committed receipt in every field but the clock.

## The two that needed undocumented arguments

Both work. Neither was invocable from the documentation as it stood, which in practice means
nobody would have run them.

**`erdos564-close-2026-09-05/sat/verify_witness.py`** takes the solver log, N, and n:

```
python verify_witness.py N12_cadical.log 12 4
```

It re-reads the SAT model, rebuilds the colouring from scratch, and brute-forces every 4-subset
rather than trusting the solver. Output on re-run matched the committed `verify_N12.txt` byte for
byte, including the full 220-bit witness string: a 2-colouring of the 220 triples of [12], 110 red
and 110 blue, with no monochromatic 4-set across all 495 subsets. Hence r_3(4) >= 13.

**`cover-C13-6-3/receipts/xverify.py`** takes the receipt file, documented in that campaign's own
`VERIFICATION.md`. It rejects the 8-block receipt, naming the two pairs it misses.

## What exit 0 means here

Exit 0 means **the verifier ran to completion**, not that a claim is true. Several of these
verifiers can run cleanly and report a negative result, and one of them does exactly that. Read the
verdict the script prints, not the exit code.

None of this is proof-assistant verification. The Lean work in these repositories is separate, and
carries its own axiom footprints.
