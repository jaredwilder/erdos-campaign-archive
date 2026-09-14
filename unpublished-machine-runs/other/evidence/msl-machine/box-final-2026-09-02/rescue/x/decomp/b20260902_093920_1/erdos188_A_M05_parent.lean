import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def UnitDist (x y : EuclideanSpace ℝ (Fin 2)) : Prop := dist x y = (1 : ℝ)

def GoodColoring (c : EuclideanSpace ℝ (Fin 2) → Bool) (k : ℕ) : Prop :=
  (∀ x y : EuclideanSpace ℝ (Fin 2), UnitDist x y → c x = true → c y = false) ∧
  (∀ p v : EuclideanSpace ℝ (Fin 2), ‖v‖ = (1 : ℝ) →
    ¬ ∀ i : Fin k, c (p + (i : ℝ) • v) = true)

def AdmissibleSet : Set ℕ :=
  {k : ℕ | ∃ c : EuclideanSpace ℝ (Fin 2) → Bool, GoodColoring c k}

theorem msl_erdos188_a_m05_parent : ∃ s : ℕ, IsLeast AdmissibleSet s := by sorry
