import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open Set

/-
The Ramsey number is represented directly by the least order of a complete
graph-free/independent-set-free obstruction.  The finite graph formulation
uses `SimpleGraph (Fin N)`, so that the underlying objects are finite.
-/

def IsClique {N : ℕ} (G : SimpleGraph (Fin N)) (s : Finset (Fin N)) : Prop :=
  ∀ ⦃u v : Fin N⦄, u ∈ s → v ∈ s → u ≠ v → G.Adj u v

def IsIndependent {N : ℕ} (G : SimpleGraph (Fin N)) (s : Finset (Fin N)) : Prop :=
  ∀ ⦃u v : Fin N⦄, u ∈ s → v ∈ s → u ≠ v → ¬G.Adj u v

def RamseyProperty (n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    ∃ s : Finset (Fin N),
      n ≤ s.card ∧ (IsClique G s ∨ IsIndependent G s)

noncomputable def ramseyNumber (n : ℕ) : ℕ :=
  sInf {N : ℕ | RamseyProperty n N}

/-- The ratio assertion in the question, for a fixed finite instance. -/
def RatioAt (R : ℕ → ℕ) (n c : ℕ) : Prop :=
  R (n + 1) ≥ (1 + c) * R n

/-- The quadratic-difference assertion in the question, for a fixed instance. -/
def DifferenceAt (R : ℕ → ℕ) (n c : ℕ) : Prop :=
  R (n + 1) - R n ≥ c * n ^ 2

/--
A decidable finite shadow of the two inequalities in the question.  The
eventual quantifiers and the positive real constant are stated below in the
main open conjecture.
-/
def LocalGrowth (R : ℕ → ℕ) (n c : ℕ) : Prop :=
  RatioAt R n c ∧ DifferenceAt R n c

theorem witness_pos :
    LocalGrowth (fun n : ℕ => 2 ^ n) 1 1 := by
  norm_num [LocalGrowth, RatioAt, DifferenceAt]

theorem witness_neg :
    ¬ LocalGrowth (fun _ : ℕ => 1) 1 1 := by
  norm_num [LocalGrowth, RatioAt, DifferenceAt]

def EventuallyRatio (R : ℕ → ℕ) : Prop :=
  ∃ c : ℚ, 0 < c ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (R (n + 1) : ℚ) / (R n : ℚ) ≥ 1 + c

def QuadraticDifferenceGrowth (R : ℕ → ℕ) : Prop :=
  ∃ c : ℚ, 0 < c ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((R (n + 1) : ℚ) - (R n : ℚ)) ≥ c * (n : ℚ) ^ 2

/--
Formalization of Erdos problem 812: whether the ratio is eventually bounded
below by `1 + c` for some `c > 0`, and whether the successive difference is
eventually much larger than `n^2`.
-/
theorem open_conjecture :
    EventuallyRatio ramseyNumber ∧
      QuadraticDifferenceGrowth ramseyNumber := by
  sorry

/-
The resolution records the known bound `R(n+1) - R(n) ≥ 4*n - 8` for `n ≥ 2`,
and the further estimate `R(n+2) - R(n) ≫ n^(2-o(1))`, attributed to
[Er91], [BEFS89], and [165].
-/

end