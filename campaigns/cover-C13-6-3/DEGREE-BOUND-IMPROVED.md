# The degree bound is 9, not 8

This supersedes the `cover20_point_degree` bound published in
[erdos-theorems](https://github.com/jaredwilder/erdos-theorems), which proves every point of a
20-block C(13,6,3) cover lies in **at least 8** blocks. The true bound is **at least 9**, and
raising it by one collapses the search space almost completely.

Found 2026-09-11 in a mining transcript that had been sitting truncated on disk; verified here from
scratch.

---

## The argument

Let `B` be a 20-block covering design on 13 points with blocks of size 6, covering every triple.
Fix a point `x` and let `r_x` be the number of blocks containing it.

Delete `x` from each of those `r_x` blocks. What remains is `r_x` subsets of size 5, drawn from the
other **12** points. Every triple through `x` must be covered, which means **every pair from those
12 points must appear in one of the 5-subsets.**

So those `r_x` blocks form a **(12, 5, 2) covering design**. Therefore

```
r_x  >=  C(12,5,2)
```

and the La Jolla value is **C(12,5,2) = 9.**

## That input was verified independently, in this repository, earlier the same day

The covering verifier shipped in this campaign settles C(12,5,2) = 9 without appeal to an external
table:

| receipt | blocks | result |
|---|---|---|
| `c8b.json` | 8 | **`EXHAUSTED_NO_COVER`** after **4,112,326,321** search nodes |
| `c9b.json` | 9 | covers all 66 pairs, confirmed from the definition |

So 8 blocks provably cannot cover, and 9 do. `C(12,5,2) = 9`, hence `r_x >= 9`.

## What the extra 1 buys

The 20 blocks have 6 points each, so the degrees sum to exactly `20 x 6 = 120`.

| bound | degree floor | slack |
|---|---|---|
| published `r_x >= 8` | 13 x 8 = 104 | **16** |
| corrected `r_x >= 9` | 13 x 9 = 117 | **3** |

Sixteen units of slack admit an enormous family of degree sequences. **Three units admit exactly
three**, enumerated completely:

| degree multiset | sum | points of degree exactly 9 |
|---|---|---|
| **12, 9¹²** | 120 | 12 |
| **11, 10, 9¹¹** | 120 | 11 |
| **10, 10, 10, 9¹⁰** | 120 | 10 |

There is no fourth. Consequently:

> **At least ten of the thirteen points have degree exactly 9**, and each such point's blocks
> induce an *optimal* 9-block (12,5,2) covering design on the remaining 12 points.

That is a rigid structural constraint on any 20-block C(13,6,3) cover, and it follows from one
covering number plus a degree count.

## Status

The improvement is an elementary argument resting on a computational input that is verified in this
repository. It is **not yet formalized** — the Lean theorem in `erdos-theorems` still carries the
weaker `8`, and updating it to `9` requires `C(12,5,2) = 9` as a Lean-side hypothesis or an
imported certificate.

The published bound is not wrong. It is weaker than what the same setup supports.
