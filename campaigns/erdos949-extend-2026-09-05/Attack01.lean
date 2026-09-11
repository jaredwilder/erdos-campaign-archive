import Mathlib

/-!
Erdős 949 — extensions of the sealed 2-fold universal theorem (campaign erdos949-extend, 2026-09-05).

Sealed baseline (kernel-checked, `Erdos949Core.lean`):
  `erdos949_finite_core`  : for every sum-free `S ⊆ {1..10}`, some `q ∈ {1..5}` has `q ∉ S ∧ 2q ∉ S`.
  `erdos949_universal`    : the same over `ℝ`.
  `erdos949_five_sharp`   : `{1,4,6}` defeats every `q ≤ 4`, so `5` is sharp.

This file proves, building verbatim on `erdos949_finite_core`:

  (b) `erdos949_universal_monoid` : the 2-fold `q ≤ 5` theorem holds over ANY additive commutative
      monoid-with-one — the reals played no role.  Instances for `ℤ`, `ℚ`, `ℂ`, and a re-derivation
      of the sealed `ℝ` statement.  FINDING: the universal statement is purely additive.

  (c) `erdos949_five_sharp_int` : sharpness transfers to `ℤ` (companion to the sealed real form).

  (d) `erdos949_threefold_bound_gt_five` / `erdos949_threefold_bound_ge_nine` :
      REFUTATION.  The `q ≤ 5` bound does NOT extend to the "tripling" problem
      (avoid `q, 2q, 3q` simultaneously).  Explicit sum-free kernel witnesses defeat every `q ≤ 5`
      (`{1,4,6,15}`) and every `q ≤ 8` (`{1,6,8,10,21}`), so the small-`q` bound for the 3-fold
      variant is at least `9`, strictly larger than the doubling bound `5`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

/-- The sealed decidable finite core (copied verbatim from `Erdos949Core.lean`). -/
theorem erdos949_finite_core :
    ∀ S ∈ (Finset.Icc 1 10).powerset,
      (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) → ∃ q ∈ Finset.Icc 1 5, q ∉ S ∧ 2 * q ∉ S := by
  decide +kernel

/-- **Erdős 949, universal 2-fold theorem over an arbitrary additive commutative monoid-with-one.**
For every sum-free `S ⊆ R` there is a natural `q ∈ {1,…,5}` with `(q : R) ∉ S` and `(2q : R) ∉ S`.
The reals in the sealed `erdos949_universal` were inessential: only `Nat.cast` additivity is used. -/
theorem erdos949_universal_monoid {R : Type*} [AddCommMonoidWithOne R]
    (S : Set R) (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 5 ∧ ((q : ℕ) : R) ∉ S ∧ ((2 * q : ℕ) : R) ∉ S := by
  classical
  let S' : Finset ℕ := (Finset.Icc 1 10).filter (fun n => ((n : ℕ) : R) ∈ S)
  have hS'mem : S' ∈ (Finset.Icc 1 10).powerset :=
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hfree : ∀ a ∈ S', ∀ b ∈ S', a + b ∉ S' := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hab' := (Finset.mem_filter.mp hab).2
    push_cast at hab'
    exact hS _ ha' _ hb' hab'
  obtain ⟨q, hq, hqS, h2qS⟩ := erdos949_finite_core S' hS'mem hfree
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hq5 : q ≤ 5 := (Finset.mem_Icc.mp hq).2
  refine ⟨q, hq1, hq5, ?_, ?_⟩
  · intro h
    exact hqS (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, by omega⟩, h⟩)
  · intro h
    exact h2qS (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h⟩)

/-- Instance over `ℤ`. -/
theorem erdos949_universal_int (S : Set ℤ) (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 5 ∧ ((q : ℕ) : ℤ) ∉ S ∧ ((2 * q : ℕ) : ℤ) ∉ S :=
  erdos949_universal_monoid S hS

/-- Instance over `ℚ`. -/
theorem erdos949_universal_rat (S : Set ℚ) (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 5 ∧ ((q : ℕ) : ℚ) ∉ S ∧ ((2 * q : ℕ) : ℚ) ∉ S :=
  erdos949_universal_monoid S hS

/-- Instance over `ℂ`. -/
theorem erdos949_universal_complex (S : Set ℂ) (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 5 ∧ ((q : ℕ) : ℂ) ∉ S ∧ ((2 * q : ℕ) : ℂ) ∉ S :=
  erdos949_universal_monoid S hS

/-- The sealed `ℝ` statement, re-derived from the general monoid form (consistency check). -/
theorem erdos949_universal_real (S : Set ℝ) (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 5 ∧ ((q : ℕ) : ℝ) ∉ S ∧ ((2 * q : ℕ) : ℝ) ∉ S :=
  erdos949_universal_monoid S hS

/-- **Sharpness over `ℤ`** (companion to the sealed `erdos949_five_sharp_real`).  The sum-free set
`{1,4,6} ⊆ ℤ` defeats every `q ≤ 4`, so the bound `5` is best possible over `ℤ` as well. -/
theorem erdos949_five_sharp_int :
    ∃ S : Set ℤ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) ∧
      ∀ q : ℕ, 1 ≤ q → q ≤ 4 → (((q : ℕ) : ℤ) ∈ S ∨ ((2 * q : ℕ) : ℤ) ∈ S) := by
  refine ⟨{1, 4, 6}, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hab
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hab with h | h | h <;> norm_num at h
  · intro q h1 h4
    interval_cases q <;> norm_num [Set.mem_insert_iff, Set.mem_singleton_iff]

/-- **Refutation, part 1.**  The `q ≤ 5` bound of the doubling theorem does NOT extend to the
tripling problem.  The sum-free set `{1,4,6,15} ⊆ ℝ` hits `{q,2q,3q}` for every `q ≤ 5`, so there
is no `q ≤ 5` with `q, 2q, 3q` all outside `S`. -/
theorem erdos949_threefold_bound_gt_five :
    ∃ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) ∧
      ∀ q : ℕ, 1 ≤ q → q ≤ 5 →
        (((q : ℕ) : ℝ) ∈ S ∨ ((2 * q : ℕ) : ℝ) ∈ S ∨ ((3 * q : ℕ) : ℝ) ∈ S) := by
  refine ⟨{1, 4, 6, 15}, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hab
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hab with h | h | h | h <;> norm_num at h
  · intro q h1 h5
    interval_cases q <;> norm_num [Set.mem_insert_iff, Set.mem_singleton_iff]

/-- **Refutation, part 2.**  The 3-fold small-`q` bound is at least `9`.  The sum-free set
`{1,6,8,10,21} ⊆ ℝ` hits `{q,2q,3q}` for every `q ≤ 8`, so no `q ≤ 8` avoids all three multiples;
in particular the tripling bound is strictly larger than the doubling bound `5`. -/
theorem erdos949_threefold_bound_ge_nine :
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

#print axioms erdos949_finite_core
#print axioms erdos949_universal_monoid
#print axioms erdos949_universal_int
#print axioms erdos949_universal_rat
#print axioms erdos949_universal_complex
#print axioms erdos949_universal_real
#print axioms erdos949_five_sharp_int
#print axioms erdos949_threefold_bound_gt_five
#print axioms erdos949_threefold_bound_ge_nine
