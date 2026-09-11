# Erdős 949 — close campaign, 2026-09-05

**Target (open).** Let `S ⊆ ℝ` contain no solution of `a + b = c` with `a,b,c ∈ S`
(sum-free, diagonal `a = b` included). Must there be `A ⊆ ℝ \ S` with `#A = 𝔠` and
`A + A ⊆ ℝ \ S`?

Formal statement: `oracle/acquisition/formal-conjectures/FormalConjectures/ErdosProblems/949.lean`
(`Erdos949.erdos_949`, `answer(sorry)`, category `research open`).

**STATUS OF THIS CAMPAIGN: NOT CLOSED.** No proof, no counterexample. What is banked is a
sharpened encirclement plus new kernel-checked reductions. Everything below is labelled
either KERNEL-CHECKED or PAPER-ONLY (= UNPROVED in this estate's sense).

---

## 0. What was already public (read before attacking)

| result | status | where |
|---|---|---|
| Sidon variant is TRUE | solved (AlphaProof), formalized | `949.lean`, `erdos_949.variants.sidon` |
| `#S < 𝔠` ⇒ conclusion | solved (Dillies' Zorn argument) | first branch of the same proof |
| `S` has the Baire property ⇒ conclusion | **reported solved** in the problem's forum thread | erdosproblems.com/forum/thread/949 |

⚠ **SOURCE CAVEAT.** `erdosproblems.com` returned HTTP 403 to every fetch attempt from this
session. The Baire-property line above comes from a web-search *summary* of that thread
(last edited 2026-01-11), **not read first-hand**. Treat it as reported, not verified.
The same summary mentions a comment reducing to sets that accumulate at the origin —
which is the trivial interval reduction, kernel-checked below as `witness_of_gap`.

## 0a. What the estate already had on 949 (and why it does not touch this question)

`erdos949-campaign-001` and `erdos949-extend-2026-09-05` bank a *finite* core
(every sum-free `S ⊆ ℝ` has `q ≤ 5` with `q ∉ S`, `2q ∉ S`; sharp) and a *countable*
Hindman result (infinite `A ⊆ ℕ` with `FS(A)`, `2·FS(A)` avoiding `S`). Neither says
anything about cardinality `𝔠`. This campaign is the first in the estate aimed at the
continuum statement itself.

---

## 1. KERNEL-CHECKED (sorry-free, 23 declarations)

Toolchain `leanprover/lean4:v4.31.0-rc1`, Mathlib rev `919544d4309104b3f19724b0e6e48c701d27948f`,
box `root@51.158.234.15:/root/peer/sub-949-close`. All 23 report exactly
`[propext, Classical.choice, Quot.sound]`; zero `sorryAx`. Receipts: `Attack0*.axioms.txt`,
`Attack0*.log`, `SHA256SUMS.txt`, `verify.json`.

### Attack01.lean — the lever, the interval witness, the Zorn core

| declaration | content | novelty |
|---|---|---|
| `sumFree_disjoint_sub` | sum-free `S` ⇒ `S ∩ (S - S) = ∅` | folklore, but it is THE lever |
| `sub_subset_compl` | `S - S ⊆ Sᶜ` | folklore |
| `witness_of_gap` | `S` misses `(-ε,ε)` ⇒ `(-ε/2, ε/2)` is a witness | trivial; matches the "accumulate at 0" reduction reported on the thread |
| `witness_of_measurable_pos` | sum-free + measurable + `volume S > 0` ⇒ conclusion | **measure-side analogue** of the reported Baire result |
| `gap_of_measurable_pos` | such an `S` is bounded away from `0` | corollary of the lever + Steinhaus |
| `exists_maximal_partial` | Zorn core in covering form (no sum-freeness needed) | re-engineering of the known Zorn step, stated so both cardinal AND measure corollaries follow |
| `cover_of_maximal` | `ℝ = S ∪ S/2 ∪ A ∪ ⋃_{a∈A}(S - a)` | as above |
| `witness_of_mk_lt_continuum` | `#S < 𝔠` ⇒ conclusion | **re-derivation of the known case** |
| `uncountable_witness_of_volume_zero` | `volume S = 0` (any `S`) ⇒ ∃ **uncountable** `A ⊆ Sᶜ` with `A + A ⊆ Sᶜ` | ZFC; superseded on paper by P1 below, so its value is that it is kernel-checked |
| `witness_of_fourfold` | `#S = 𝔠`, `t ∈ S`, `(S+S+2t) ∩ S = ∅` ⇒ `S + t` is a witness | **the four-fold reduction**: sum-freeness gives `S + t ⊆ Sᶜ` for free, so the whole problem is about 4-fold sums |
| `measurable_dichotomy` | measurable ⇒ witness, or (null) uncountable partial witness | assembly |
| `control_Ico_sumFree`, `control_Ico_witness`, `control_witness_not_trivial` | non-vacuity controls (`[1,2)` is a positive-measure sum-free set; `Witness` FAILS for `S = univ`) | — |

### Attack02.lean — the covering reduction and the transfer principle

| declaration | content | novelty |
|---|---|---|
| `witness_of_no_small_cover` | if `ℝ` is **not** the union of `< 𝔠` translates of `S ∪ S/2`, the conclusion holds | **new reduction**, strictly generalises `#S < 𝔠`; confines the open problem to *translation-large* sets |
| `witness_of_mk_lt_continuum'` | the known case re-derived FROM that reduction (proving the generalisation is strict in content) | — |
| `sumFree_preimage` | sum-freeness pulls back along additive maps | folklore |
| `witness_of_preimage` | **transfer principle**: the conclusion pulls back along any injective `φ : ℝ →+ ℝ`; so one may WLOG replace `S` by `S ∩ G` for any `ℚ`-subspace `G` of dimension `𝔠` | easy but load-bearing for future attacks |
| `witness_of_addClosed` | a continuum-sized additively closed set avoiding `S` is a witness | trivial |

### Attack03.lean — measure branch sharpened to INNER measure

| declaration | content | novelty |
|---|---|---|
| `gap_of_measurable_subset_pos` | sum-free `S` containing ANY measurable set of positive measure is bounded away from `0` | **strengthens** `witness_of_measurable_pos`: `S` itself need not be measurable |
| `witness_of_measurable_subset_pos` | positive **inner** measure ⇒ conclusion | as above |
| `inner_measure_zero_of_no_witness` | a counterexample has inner measure `0` (every measurable subset null) | contrapositive, kernel-checked |
| `accumulates_at_zero_of_no_witness` | a counterexample accumulates at `0` | contrapositive, kernel-checked |

---

## 2. PAPER-ONLY — recorded, argued, **NOT kernel-checked (UNPROVED)**

These are complete arguments on paper. They are **not** banked as Lean because the missing
dependency is not in Mathlib. Do not cite them as proved.

**P1 (null ⇒ conclusion, ZFC).** Let `S` be Lebesgue-null (sum-freeness not needed).
`E = {(x,y) : x + y ∈ S}` is null in `ℝ²` (the shear `(x,y) ↦ (x+y, y)` is a measure-preserving
linear automorphism carrying `S × ℝ` to `E`). `G = {x : x ∉ S ∧ 2x ∉ S}` is conull.
By **Mycielski's theorem** (measure version) applied to the conull relation
`R = (Gᶜ × Gᶜ)ᶜ ∩ Eᶜ` there is a perfect `P` with every off-diagonal pair from `P` in `R`;
a perfect set has cardinality `𝔠`, `P ⊆ G` gives the diagonal and the `A ⊆ Sᶜ` requirement.
So `A = P` is a witness. **Missing dependency: Mycielski/Kuratowski perfect-set theorem —
absent from Mathlib (grep: no `ycielski`).**

**P2 (meager ⇒ conclusion, ZFC).** Identical with the category version of Mycielski (the
shear is a homeomorphism, so `E` is meager).

**P3 (measurable ⇒ conclusion, ZFC).** Positive measure: kernel-checked
(`witness_of_measurable_pos`, in fact the inner-measure form). Null: P1. **This is the
measure analogue of the reported Baire-property result and, as far as we could read, is
not on the problem page.** Its positive-measure half is banked; its null half is P1.

**P4 (Baire property ⇒ conclusion, ZFC).** Non-meager with BP: Pettis' difference theorem
gives `S₀ - S₀ ⊇` a neighbourhood of `0` for a non-meager BP `S₀ ⊆ S`, and the lever
`S ∩ (S - S) = ∅` then shows `S` misses that neighbourhood, so `witness_of_gap` applies.
Meager: P2. This reproduces the result reported on the forum thread. **Missing dependency:
Pettis difference theorem — also absent from Mathlib.**

---

## 3. The sharpened encirclement — what a counterexample must look like

Assembling the kernel-checked contrapositives (K) and the paper arguments (P), a sum-free
`S ⊆ ℝ` refuting Erdős 949 must satisfy **all** of:

1. `#S = 𝔠`  (K: `witness_of_mk_lt_continuum`).
2. `S` accumulates at `0`  (K: `accumulates_at_zero_of_no_witness`).
3. `S` has **inner Lebesgue measure 0** — every measurable subset is null
   (K: `inner_measure_zero_of_no_witness`).
4. `S` is **not** null  (P1) and **not** meager (P2), and contains no non-meager subset with
   the Baire property (P4). With (3): `S` is outer-full-ish but inner-null — a
   **saturated-non-measurable / Vitali-like** shape.
5. `S` is **translation-large**: `ℝ` IS the union of `< 𝔠` translates of `S ∪ S/2`
   (K: `witness_of_no_small_cover`).
6. For **every** `t ∈ S`, `(S + S + 2t) ∩ S ≠ ∅` (K: `witness_of_fourfold`) — i.e. the
   4-fold sumset always folds back into `S`.
7. `Sᶜ` contains no continuum-sized additively closed set (K: `witness_of_addClosed`).
8. All of the above persists after restricting to **every** `ℚ`-subspace of dimension `𝔠`
   (K: `witness_of_preimage`).

Point (5) is compatible with (3)–(4): a Vitali set has inner measure `0` and countably many
of its translates cover `ℝ`. So the encirclement does not itself refute the existence of a
counterexample — it says exactly where one would have to live.

## 4. Bound improvement banked

For an arbitrary **null** `S`, the previously available guarantee in this estate was a
*countable* witness (Hindman route, `erdos949-campaign-001`). `uncountable_witness_of_volume_zero`
raises that to an **uncountable** witness in ZFC, kernel-checked; and on paper (P1) to the
full `𝔠`. No improvement is claimed for the general (non-null, non-meager) case.

## 5. Honest next moves

* Formalize Mycielski's theorem (measure + category) in Lean — this alone converts P1–P4 into
  kernel-checked results and would settle the measurable and BP cases inside the estate.
  Expect a Cantor-scheme construction; not attempted here (a session-sized but not
  session-remaining job).
* Attack the residual case: sum-free, inner-null, translation-large, accumulating at `0`.
  Either (a) build such a set by transfinite recursion and try to defeat all `𝔠`-sized
  candidate witnesses (the obstruction is that there are `2^𝔠` candidates, so a counterexample
  construction needs a structural, not enumerative, kill), or (b) find an argument that
  turns condition (6) into a contradiction with (5).
* `noveltyforge` was **not** run. No novelty claim is machine-adjudicated here; the labels
  in §1 are relative to what §0 records.
