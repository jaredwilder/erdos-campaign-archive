import Mathlib


noncomputable section
open scoped BigOperators
/-!
A finite version of the admissibility condition from Erdős problem 875.
The indices are finite, so the relevant subset-sum conditions are decidable.
-/

def subsetSum {n : ℕ} (s : Fin n → ℕ) (I : Finset (Fin n)) : ℕ :=
  ∑ i ∈ I, s i

def FiniteAdmissible {n : ℕ} (s : Fin n → ℕ) : Prop :=
  StrictMono s ∧
    ∀ I J : Finset (Fin n),
      I.card ≠ J.card → subsetSum s I ≠ subsetSum s J

def FiniteQuestion {n : ℕ} (s : Fin (n + 1) → ℕ) (c : ℕ) : Prop :=
  FiniteAdmissible s ∧
    ∀ i : Fin n,
      s (Fin.castSucc i) ≤ s (Fin.succ i) ∧
      s (Fin.succ i) - s (Fin.castSucc i) ≤ (i.val + 1) ^ c

/-- The infinite version: `a n` represents the (n+1)-st term of the sequence. -/
def PolynomialGap (c : ℕ) : Prop :=
  ∃ a : ℕ → ℕ,
    StrictMono a ∧
      (∀ I J : Finset ℕ,
        I.card ≠ J.card →
          (∑ i ∈ I, a i) ≠ ∑ j ∈ J, a j) ∧
      (∀ n : ℕ, a (n + 1) - a n ≤ (n + 1) ^ c)

/-- A two-term admissible sequence with the required gap bound for exponent 1. -/
theorem witness_pos :
    FiniteQuestion (![1, 2] : Fin 2 → ℕ) 1 := by
  unfold FiniteQuestion FiniteAdmissible StrictMono
  decide

/-- The same two-term shape fails when the gap is required to be bounded by n^0. -/
theorem witness_neg :
    ¬ FiniteQuestion (![1, 3] : Fin 2 → ℕ) 0 := by
  unfold FiniteQuestion FiniteAdmissible StrictMono
  decide

/-- Erdős problem 875: determine the possible polynomial gap exponents. -/
theorem erdos_875_question :
    ∃ c : ℕ, PolynomialGap c := by
  sorry

end