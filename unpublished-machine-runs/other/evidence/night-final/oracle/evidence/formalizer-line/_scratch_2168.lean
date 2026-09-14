import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- The least prime factor, extended by `0` on inputs below `2`. -/
def leastPrimeFactor (m : ℕ) : ℕ :=
  if 2 ≤ m then Nat.minFac m else 0

/-- The bound `k^2 + 1` from the question. -/
def polynomialBound (k : ℕ) : ℕ :=
  k ^ 2 + 1

/-- A finite, decidable truncation of the assertion at `n`. -/
def boundedGood (n K : ℕ) (bound : ℕ → ℕ) : Prop :=
  ∃ k ∈ Finset.range K, leastPrimeFactor (n + k) > bound k

/-- The first assertion in the problem. -/
def polynomialPredicate (n : ℕ) : Prop :=
  ∃ k : ℕ, leastPrimeFactor (n + k) > k ^ 2 + 1

/-- The assertion obtained after replacing `k^2 + 1` by
`e^((1 + ε) * sqrt k) + Cε`. -/
def exponentialPredicate (ε Cε : ℝ) (n : ℕ) : Prop :=
  ∃ k : ℕ,
    (leastPrimeFactor (n + k) : ℝ) >
      Real.exp ((1 + ε) * Real.sqrt (k : ℝ)) + Cε

theorem witness_pos : boundedGood 2 1 polynomialBound := by
  refine ⟨0, by simp, ?_⟩
  norm_num [leastPrimeFactor, polynomialBound, Nat.minFac]

theorem witness_neg : ¬ boundedGood 1 1 polynomialBound := by
  intro h
  rcases h with ⟨k, hk, hineq⟩
  have hk' : k < 1 := Finset.mem_range.mp hk
  have hk0 : k = 0 := by omega
  subst k
  norm_num [leastPrimeFactor, polynomialBound] at hineq

/-- Formal statement of Erdős problem 680. -/
theorem erdos_680 :
    (∀ᶠ n : ℕ in Filter.atTop, polynomialPredicate n) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ Cε : ℝ, 0 < Cε ∧
          ¬ (∀ᶠ n : ℕ in Filter.atTop, exponentialPredicate ε Cε n)) := by
  sorry

end