import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- The number of ordered representations of `n` as a difference of two
elements of a finite set. -/
def differenceCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  ((A.product A).filter (fun p => p.1 - p.2 = n)).card

/-- A finite approximation to being a perfect difference set: every positive
integer up to `N` has exactly one ordered difference representation. -/
def perfectThrough (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 1 N, differenceCount A n = 1

/-- The property that a sequence gives the first coordinates of difference
representations whose ratios are unbounded along arbitrarily large indices. -/
def hasUnboundedFirstCoordinate (A : Set ℕ) : Prop :=
  ∃ a b : ℕ → ℕ,
    (∀ n : ℕ, 1 ≤ n →
      a n ∈ A ∧ b n ∈ A ∧ a n - b n = n) ∧
    (∀ K N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ 1 ≤ n ∧ K * n ≤ a n)

/-- Every positive integer has a unique representation as a difference. -/
def perfectDifferenceSet (A : Set ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃! p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 - p.2 = n

/-- The cubic upper bound mentioned for the greedy construction. -/
def cubicBound (a : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → a n ≤ C * n ^ 3

theorem witness_pos :
    perfectThrough ({0, 1} : Finset ℕ) 1 := by
  unfold perfectThrough
  intro n hn
  have hn' : n = 1 := by
    simp only [Finset.mem_Icc] at hn
    omega
  subst n
  native_decide

theorem witness_neg :
    ¬ perfectThrough ({0, 1} : Finset ℕ) 2 := by
  intro h
  unfold perfectThrough at h
  have h2 := h 2 (by simp)
  have hne : differenceCount ({0, 1} : Finset ℕ) 2 ≠ 1 := by
    native_decide
  exact hne h2

/-- Erdős problem #1194: for a perfect difference set, the ratios `aₙ / n`
are unbounded along arbitrarily large indices (equivalently, their limsup is
infinite). -/
theorem erdos_problem_1194 :
    ∀ A : Set ℕ, perfectDifferenceSet A →
      hasUnboundedFirstCoordinate A := by
  sorry

end