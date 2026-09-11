import Mathlib

/-!
Erdős 949 — the 3-fold ("tripling") bound is **exactly 9** (campaign erdos949-extend, 2026-09-05).

## The gap this closes

`TERMINAL.json` recorded, in `open[0]`:

  > 3-fold POSITIVE bound: every sum-free `S` has `q ∈ {1..9}` with `q, 2q, 3q` all outside `S`
  > … status CONJECTURED_not_formalized
  > reason: finite core would be `decide` over `2^27` subsets of `{1..27}`; infeasible for
  >         decide+kernel.  Needs a non-brute-force argument.

The `2^27` figure came from enumerating SUBSETS.  That is the wrong search space.

## The non-brute-force argument (the reason this file exists)

Non-sum-freeness is UPWARD closed: if `T ⊆ S` already contains `a, b, a+b` then so does `S`.
A counterexample `S` must, for each `q ∈ {1,…,9}`, contain at least one of `q, 2q, 3q`.  Choosing
one such element per `q` extracts a **minimal blocker** `T ⊆ S` with at most 9 elements, and there
are only `3^9 = 19683` of them.  So it suffices to check that every minimal blocker is
non-sum-free — `19683` cases over 9-element lists instead of `2^27 = 134{,}217{,}728` subsets, a
`6800×` reduction, and each case is 6.6× smaller.

Independently searched first (`scratchpad/threefold.py`, exhaustive over sum-free subsets of the
18 relevant values `{1,2,3,4,5,6,7,8,9,10,12,14,15,16,18,21,24,27}`):

  M ≤ 8 : counterexamples exist (M=8 witness `{1,6,8,10,21}` — the one Attack01 already sealed)
  M = 9 : no counterexample

and no proper subset of `{1,…,9}` suffices (`scratchpad/minimal_q.py`), so all nine multipliers
are load-bearing and `19683` is the true certificate size.

## What is proved here

`threefold_blocker_core`   — kernel `decide`: all `3^9` minimal blockers are non-sum-free.
`erdos949_threefold_universal` — for every sum-free `S` in ANY `AddCommMonoidWithOne` there is
                             `q ∈ {1,…,9}` with `q, 2q, 3q` all outside `S`.
`erdos949_threefold_real`  — the `ℝ` instance.
`erdos949_threefold_nine_sharp` — `9` is best possible: Attack01's sum-free `{1,6,8,10,21}`
                             blocks every `q ≤ 8`.

Together with Attack01's `erdos949_threefold_bound_ge_nine`, the 3-fold bound is EXACTLY 9,
against the doubling bound of exactly 5.
-/

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Erdos949Threefold

/-- A minimal blocker: for each `q ∈ {1,…,9}` the chosen multiple `(cᵩ+1)·q ∈ {q, 2q, 3q}`. -/
def blk9 (c1 c2 c3 c4 c5 c6 c7 c8 c9 : ℕ) : List ℕ :=
  [(c1 + 1) * 1, (c2 + 1) * 2, (c3 + 1) * 3, (c4 + 1) * 4, (c5 + 1) * 5,
   (c6 + 1) * 6, (c7 + 1) * 7, (c8 + 1) * 8, (c9 + 1) * 9]

/-- **The finite core.**  Every one of the `3^9 = 19683` minimal blockers contains `a`, `b` and
`a + b`, i.e. no minimal blocker is sum-free.  Checked by the Lean kernel (`decide +kernel`;
`native_decide` is NOT used). -/
theorem threefold_blocker_core :
    ∀ c1 < 3, ∀ c2 < 3, ∀ c3 < 3, ∀ c4 < 3, ∀ c5 < 3, ∀ c6 < 3, ∀ c7 < 3, ∀ c8 < 3, ∀ c9 < 3,
      ∃ a ∈ blk9 c1 c2 c3 c4 c5 c6 c7 c8 c9, ∃ b ∈ blk9 c1 c2 c3 c4 c5 c6 c7 c8 c9,
        a + b ∈ blk9 c1 c2 c3 c4 c5 c6 c7 c8 c9 := by
  decide +kernel

/-- **Erdős 949, 3-fold universal theorem, bound 9.**  For every sum-free `S` in an arbitrary
additive commutative monoid-with-one there is `q ∈ {1,…,9}` with `(q : R)`, `(2q : R)` and
`(3q : R)` all outside `S`.  (Attack01 showed the doubling bound `5` does NOT suffice here.) -/
theorem erdos949_threefold_universal {R : Type*} [AddCommMonoidWithOne R]
    (S : Set R) (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 9 ∧
      ((q : ℕ) : R) ∉ S ∧ ((2 * q : ℕ) : R) ∉ S ∧ ((3 * q : ℕ) : R) ∉ S := by
  classical
  by_contra hcon
  -- For each `q ∈ {1,…,9}` some multiplier `j ∈ {1,2,3}` lands in `S`.
  have hpick : ∀ q : ℕ, 1 ≤ q → q ≤ 9 → ∃ j : ℕ, j < 3 ∧ (((j + 1) * q : ℕ) : R) ∈ S := by
    intro q hq1 hq9
    by_contra hno
    push_neg at hno
    refine hcon ⟨q, hq1, hq9, ?_, ?_, ?_⟩
    · have := hno 0 (by norm_num); simpa using this
    · have := hno 1 (by norm_num); simpa using this
    · have := hno 2 (by norm_num); simpa using this
  obtain ⟨d1, hd1, hs1⟩ := hpick 1 (by norm_num) (by norm_num)
  obtain ⟨d2, hd2, hs2⟩ := hpick 2 (by norm_num) (by norm_num)
  obtain ⟨d3, hd3, hs3⟩ := hpick 3 (by norm_num) (by norm_num)
  obtain ⟨d4, hd4, hs4⟩ := hpick 4 (by norm_num) (by norm_num)
  obtain ⟨d5, hd5, hs5⟩ := hpick 5 (by norm_num) (by norm_num)
  obtain ⟨d6, hd6, hs6⟩ := hpick 6 (by norm_num) (by norm_num)
  obtain ⟨d7, hd7, hs7⟩ := hpick 7 (by norm_num) (by norm_num)
  obtain ⟨d8, hd8, hs8⟩ := hpick 8 (by norm_num) (by norm_num)
  obtain ⟨d9, hd9, hs9⟩ := hpick 9 (by norm_num) (by norm_num)
  -- The whole minimal blocker sits inside `S`.
  have key : ∀ n ∈ blk9 d1 d2 d3 d4 d5 d6 d7 d8 d9, ((n : ℕ) : R) ∈ S := by
    intro n hn
    simp only [blk9, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs1
    · exact hs2
    · exact hs3
    · exact hs4
    · exact hs5
    · exact hs6
    · exact hs7
    · exact hs8
    · exact hs9
  -- But the core says the blocker is not sum-free.
  obtain ⟨a, ha, b, hb, hab⟩ :=
    threefold_blocker_core d1 hd1 d2 hd2 d3 hd3 d4 hd4 d5 hd5 d6 hd6 d7 hd7 d8 hd8 d9 hd9
  have hA := key a ha
  have hB := key b hb
  have hAB := key (a + b) hab
  have hcast : ((a + b : ℕ) : R) = ((a : ℕ) : R) + ((b : ℕ) : R) := by push_cast; ring
  rw [hcast] at hAB
  exact hS _ hA _ hB hAB

/-- The `ℝ` instance of the 3-fold bound. -/
theorem erdos949_threefold_real (S : Set ℝ) (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 9 ∧
      ((q : ℕ) : ℝ) ∉ S ∧ ((2 * q : ℕ) : ℝ) ∉ S ∧ ((3 * q : ℕ) : ℝ) ∉ S :=
  erdos949_threefold_universal S hS

/-- **Sharpness: the bound `9` cannot be lowered to `8`.**  (Same witness as Attack01's
`erdos949_threefold_bound_ge_nine`, restated here so that this file states the exact value.) -/
theorem erdos949_threefold_nine_sharp :
    ∃ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) ∧
      ∀ q : ℕ, 1 ≤ q → q ≤ 8 →
        (((q : ℕ) : ℝ) ∈ S ∨ ((2 * q : ℕ) : ℝ) ∈ S ∨ ((3 * q : ℕ) : ℝ) ∈ S) := by
  refine ⟨{1, 6, 8, 10, 21}, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hab
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      rcases hab with h | h | h | h | h <;> norm_num at h
  · intro q h1 h8
    interval_cases q <;> norm_num [Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Known-answer control: the conclusion is false for `S = univ` (not sum-free), so the sum-free
hypothesis is load-bearing and `erdos949_threefold_universal` is not vacuous. -/
theorem erdos949_threefold_control :
    ¬ ∃ q : ℕ, 1 ≤ q ∧ q ≤ 9 ∧
      ((q : ℕ) : ℝ) ∉ (Set.univ : Set ℝ) ∧ ((2 * q : ℕ) : ℝ) ∉ (Set.univ : Set ℝ) ∧
      ((3 * q : ℕ) : ℝ) ∉ (Set.univ : Set ℝ) := by
  rintro ⟨q, -, -, h, -, -⟩
  exact h (Set.mem_univ _)

end Erdos949Threefold

#print axioms Erdos949Threefold.threefold_blocker_core
#print axioms Erdos949Threefold.erdos949_threefold_universal
#print axioms Erdos949Threefold.erdos949_threefold_real
#print axioms Erdos949Threefold.erdos949_threefold_nine_sharp
#print axioms Erdos949Threefold.erdos949_threefold_control
