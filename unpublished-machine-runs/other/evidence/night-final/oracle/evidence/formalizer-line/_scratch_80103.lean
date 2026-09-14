import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical

def DecreasesAt {α : Type} [LT α] (f : ℕ → α) (n : ℕ) : Prop :=
  1 ≤ n ∧ f (n + 1) < f n

def A {α : Type} [LT α] (f : ℕ → α) : Set ℕ :=
  {n | DecreasesAt f n}

def ErdosAdditive (f : ℕ → ℝ) : Prop :=
  ∀ ⦃a b : ℕ⦄, Nat.Coprime a b → f (a * b) = f a + f b

local notation "Additive" => ErdosAdditive

noncomputable def badCount (f : ℕ → ℝ) (X : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 X).filter (fun n => DecreasesAt f n)).card

def SparseDecrease (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (badCount f X : ℝ) ≤ ε * (X : ℝ)

def IsLogarithmic (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, f n = c * Real.log (n : ℝ)

theorem erdos_problem_1122 :
    ∀ f : ℕ → ℝ, Additive f → SparseDecrease f → IsLogarithmic f := by
  sorry

theorem witness_pos :
    1 ∈ A (fun n : ℕ => -(n : ℤ)) := by
  norm_num [A, DecreasesAt]

theorem witness_neg :
    ¬ (1 ∈ A (fun _ : ℕ => (0 : ℤ))) := by
  norm_num [A, DecreasesAt]

end