# What is actually in here

This repository holds 266 campaigns published entire, and the front page says a sample of twenty
found *"one proved theorem, four refutations, and seven that produced nothing."* That is true of a
random sample, and it is also why a reader walks straight past the campaigns that did land.

Eleven of them carry **kernel-checked, sorry-free Lean**. This file names them.

**None of these closes an Erdos problem.** Several do something more useful than a partial result:
they refute a stated conjecture, or pin the open region down to one named class.

---

## The two that refute a published or stated conjecture

### `erdos592-close-2026-09-05` — ordinal Ramsey, 28 kernel-checked theorems

A **proven-exhaustive and proven-exclusive five-way classification** of the ordinals, which pins the
open region to a single class.

- `frontier_exhaustive` and `frontier_exclusive` — the five classes partition the ordinals
- `omega_pow_three_least` — **ω³ is the LEAST open instance**, the smallest undecided concrete case
- `galvin_larson_conjecture_false` — **refutes the obvious answer**, with an ω⁴ counterexample
- `erdos592_reduces_to_ClassD` — everything remaining reduces to β = ω^γ with `indecCount(γ) = 3`
- `no_monotone_bridge` — no monotonicity argument can carry between the regions

### `erdos593-close-2026-09-05` — obligatory hypergraphs

The conjectural characterization stated in the formal-conjectures file is **FALSE, refuted three
independent ways**, each refutation computed against a different literature theorem.

`frontier_pinned` proves a strict chain — loose forests < OBLIGATORY < linear and 3-partite <
2-colourable — **all strict, with the witnesses `C_4^(3)`, `C_3^(3)`, `K_4^(3)` named**. And
`no_monotone_bridge`: no combination of the two known necessary conditions can characterize the
obligatory class.

---

## The one that moves a ladder

### `eg411-omega67-2026-09-05` — the ω ≤ 6 rung

`solution_omega_le_six_classified`: **every solution of `3·φ(n) = 2n + 2` with `ω(n) ≤ 6` is one of
`5, 35, 1295, 1679615`, and the ω = 6 stratum is empty.**

Plus `exceptional_high_omega_seven`, unconditional: any exceptional prime other than 7 and 47 comes
from a solution with **at least seven** distinct prime factors.

This advances a ladder whose previous rung stood at ω ≤ 5.

---

## The one that is reusable

### `irrationality-blade-2026-09-05`

`irrational_of_denominator_squeeze` — if for every positive `q` one can produce a natural `D` and an
integer `P` with `0 < D·x − P` and `q·(D·x − P) < 1`, then `x` is irrational. Plus a tail form,
`irrational_of_head_clearing`, for indexed multiplier families.

Axiom footprint `[propext, Classical.choice, Quot.sound]`. It is written as a **reusable core** for
Erdos problems 243, 247, 249, 251, 257, 260, 1049 and 68.

---

## The rest, with what they banked

| campaign | kernel theorems | what landed |
|---|---|---|
| `erdos146-attack-2026-09-05` | **37** | **"AKS is insufficient, machine-checked"** — for every r >= 1 an explicit `f` refuting the cited conclusion, so no black-box derivation can prove the conjecture. Plus: proving the bound for `Fin m` graphs for every m proves it in every universe. |
| `erdos20-close-2026-09-05` | **19** | The classical sunflower sandwich, including the **Erdos-Rado sunflower lemma in Finset form, which is not in Mathlib**. Exact values `f(1,k) = k` and `f(n,2) = 2`, and an improved lower-bound base `6^t < f(2t,3)`. |
| `erdos74-close-2026-09-05` | **16** | The first machine-checked content for a file that carried only two lemmas. `colorable_of_bounded_defect` via de Bruijn-Erdos compactness. The rate, which is the entire open content, is untouched and said to be. |
| `erdos39-close-2026-09-05` | **13** | Sidon density: cardinality bound, maximal-set density, greedy density, existence of dense Sidon sets. Formalizes classical bounds; **no novelty claimed**. |
| `erdos138-close-2026-09-05` | 10 sealed | The obstruction mapped precisely: the transported Berlekamp bound **loses exactly `2^(g+1)`**, and Rankin-type large prime gaps make the transport fail on an infinite set of k. |
| `erdos143-close-2026-09-05` | 5 | The packing theorem `|A ∩ (-∞, 2X)| <= ceil(X)`, upper density 1/2 proved optimal. Flags its own **suspected prior-art collision** with a known elementary observation. |
| `erdos89-close-2026-09-05` | 2 | The elementary `Ω(√n)` distinct-distances bound, shipped **with a gap ledger proving it is asymptotically negligible** against the `n/√(log n)` target. |

---

## How to read this

Every campaign above states its own ceiling, and several state plainly that what they proved is far
below what the problem asks. `erdos89` is the clearest case: it proves a bound and then proves, in
the same campaign, that its own bound does not matter asymptotically.

The other 255 campaigns are published for the same reason the seven that produced nothing are: a
record that only contains its successes cannot be checked.
