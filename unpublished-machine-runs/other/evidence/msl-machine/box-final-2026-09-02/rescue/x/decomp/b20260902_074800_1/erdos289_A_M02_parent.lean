import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset
open Filter

def schemeStruct (k : ℕ) (I : Fin k → ℕ × ℕ) : Prop :=
  (∀ i : Fin k, (I i).1 < (I i).2) ∧
  ∀ i j : Fin k, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1

def Erdos289Sum (k : ℕ) (I : Fin k → ℕ × ℕ) : ℚ :=
  ∑ i : Fin k, ∑ n ∈ Icc (I i).1 (I i).2, ((n : ℕ)⁻¹ : ℚ)

theorem msl_erdos289_a_m02_parent : ∀ᶠ k : ℕ in atTop, ∃ I : Fin k → ℕ × ℕ, schemeStruct k I ∧ Erdos289Sum k I = (1 : ℚ) := by sorry
