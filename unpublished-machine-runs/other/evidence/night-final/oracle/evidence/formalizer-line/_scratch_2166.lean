import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open Filter
/-
The index `0` below represents the source index `1`; this shift avoids
having to treat the first difference separately.
-/
def PrimeConvexSequence (q : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, Nat.Prime (q n)) ∧
    (∀ n : ℕ, q n < q (n + 1)) ∧
      (∀ n : ℕ, q (n + 1) - q n ≤ q (n + 2) - q (n + 1))

def QuadraticDivergence (q : ℕ → ℕ) : Prop :=
  Tendsto (fun n : ℕ => (q n : ℝ) / ((n : ℝ) ^ 2)) atTop atTop

/-
A finite, decidable version used for concrete kernel-checkable witnesses.
The parameter `N` gives `N + 2` consecutive primes.
-/
def FiniteAdmissible (N : ℕ) (q : Fin (N + 2) → ℕ) : Prop :=
  (∀ i : Fin (N + 2), Nat.Prime (q i)) ∧
    (∀ i : Fin (N + 1),
      q ⟨i.val, by omega⟩ < q ⟨i.val + 1, by omega⟩) ∧
      (∀ i : Fin N,
        q ⟨i.val + 1, by omega⟩ - q ⟨i.val, by omega⟩ ≤
          q ⟨i.val + 2, by omega⟩ - q ⟨i.val + 1, by omega⟩)

/-- The three primes `2, 3, 5` satisfy the finite convexity condition. -/
theorem witness_pos :
    FiniteAdmissible 1 (![2, 3, 5] : Fin 3 → ℕ) := by
  unfold FiniteAdmissible
  constructor
  · intro i
    fin_cases i <;> norm_num
  · constructor
    · intro i
      fin_cases i <;> norm_num
    · intro i
      fin_cases i <;> norm_num

/-- Repeating `3` makes the strict-increase condition fail. -/
theorem witness_neg :
    ¬ FiniteAdmissible 1 (![2, 3, 3] : Fin 3 → ℕ) := by
  intro h
  unfold FiniteAdmissible at h
  have h' := h.2.1 (⟨1, by omega⟩ : Fin (1 + 1))
  norm_num at h'

/-- The decimal lower-bound constant appearing in the recorded resolution. -/
def richterLowerBound : ℝ := 0.352

/-- Erdos problem 455: whether the quadratic ratio must tend to infinity. -/
theorem erdos_455 :
    ∀ q : ℕ → ℕ, PrimeConvexSequence q → QuadraticDivergence q := by
  sorry

end