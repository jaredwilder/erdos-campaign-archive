import Mathlib

/-!
# JSPACE SHOT 1 — the Lean fire point (★), general refutation.

The shot asks the kernel to decide, for an arbitrary induced tournament `U`,

  (★)   Σ_{x ∈ U} d⁻(x)(d⁻(x) - 1)  ≤  |U|(|U|-1)(|U|-3) / 4 .

We refute it for every `n ≥ 2` with the transitive tournament, and we compute the
exact size of the failure: the overshoot is `(n³ - n)/12`, i.e. cubic in `n`.
-/

namespace JSpaceStar

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A tournament: an irreflexive orientation in which every unordered pair is oriented. -/
structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

/-- `d⁻(x)`: the number of vertices that beat `x`. -/
def indeg (T : Tournament V) (x : V) : ℕ :=
  (univ.filter (fun y => T.beats y x)).card

/-- The left-hand side of (★), over `ℤ`. -/
def lhs (T : Tournament V) : ℤ :=
  ∑ x : V, (indeg T x : ℤ) * ((indeg T x : ℤ) - 1)

/-- The right-hand side of (★) with the `/4` cleared. -/
def rhs4 (T : Tournament V) : ℤ :=
  (Fintype.card V : ℤ) * ((Fintype.card V : ℤ) - 1) * ((Fintype.card V : ℤ) - 3)

/-- (★) itself, denominator cleared: `4 · LHS ≤ n(n-1)(n-3)`. -/
def StarBound (T : Tournament V) : Prop := 4 * lhs T ≤ rhs4 T

/-- The transitive tournament on `Fin n`: `a` beats `b` iff `a < b`. -/
def trans (n : ℕ) : Tournament (Fin n) where
  beats a b := a < b
  dec := inferInstance
  irrefl a := lt_irrefl a
  tot a b h := by
    constructor
    · intro hab hba; exact absurd (hab.trans hba) (lt_irrefl a)
    · intro hba; exact lt_of_le_of_ne (not_lt.mp hba) h

@[simp] lemma indeg_trans (n : ℕ) (x : Fin n) : indeg (trans n) x = x.val := by
  classical
  have h : (univ.filter (fun y : Fin n => y < x)) = Finset.Iio x := by
    ext y; simp
  simp only [indeg, trans]
  rw [h, Fin.card_Iio]

/-- `3 · Σ_{k<n} k(k-1) = n(n-1)(n-2)`: the transitive tournament realises `2·C(n,3)`. -/
lemma sum_sq_range (n : ℕ) :
    3 * (∑ k ∈ range n, (k : ℤ) * ((k : ℤ) - 1)) = (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

lemma lhs_trans (n : ℕ) : 3 * lhs (trans n) = (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) := by
  have : lhs (trans n) = ∑ k ∈ range n, (k : ℤ) * ((k : ℤ) - 1) := by
    simp only [lhs, indeg_trans]
    exact Fin.sum_univ_eq_sum_range (fun k => (k : ℤ) * ((k : ℤ) - 1)) n
  rw [this, sum_sq_range]

/-- **THE OVERSHOOT IS EXACT AND CUBIC.**
`12·LHS - 3·(n(n-1)(n-3)) = n³ - n` for the transitive tournament. -/
theorem star_overshoot (n : ℕ) :
    12 * lhs (trans n) - 3 * rhs4 (trans n) = (n : ℤ)^3 - (n : ℤ) := by
  have h := lhs_trans n
  simp only [rhs4, Fintype.card_fin]
  linarith [h]

/-- **(★) IS FALSE** for every `n ≥ 2`. -/
theorem star_refuted (n : ℕ) (hn : 2 ≤ n) : ¬ StarBound (trans n) := by
  intro hcon
  have hgap := star_overshoot n
  have hn2 : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hfac : (n : ℤ)^3 - (n : ℤ) = (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) + 1) := by ring
  have hpos : (0 : ℤ) < (n : ℤ)^3 - (n : ℤ) := by
    rw [hfac]
    have h1 : (0:ℤ) < (n:ℤ) := by linarith
    have h2 : (0:ℤ) < (n:ℤ) - 1 := by linarith
    have h3 : (0:ℤ) < (n:ℤ) + 1 := by linarith
    exact mul_pos (mul_pos h1 h2) h3
  simp only [StarBound] at hcon
  linarith

/-- Concretely at `n = 4`: LHS = 8, the bound allows 3. -/
example : 4 * lhs (trans 4) = 32 ∧ rhs4 (trans 4) = 12 := by
  constructor
  · have := lhs_trans 4; norm_num at this ⊢; linarith
  · simp [rhs4]

end JSpaceStar

#print axioms JSpaceStar.star_refuted
#print axioms JSpaceStar.star_overshoot
