import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset

import Mathlib
open Finset

def ValidIntervals (k : Nat) (I : Fin k → Nat × Nat) : Prop :=
  (∀ i : Fin k, (I i).1 < (I i).2) ∧
  (∀ i j : Fin k, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1)

def SumsToOne (k : Nat) (I : Fin k → Nat × Nat) : Prop :=
  (∑ i : Fin k, ∑ n ∈ Finset.Icc (I i).1 (I i).2, (((n : Nat) : ℚ)⁻¹)) = (1 : ℚ)

theorem msl_erdos289_a_m02_c1 : ∀ᶠ k : ℕ in atTop, ∃ I : Fin k → ℕ × ℕ, ValidIntervals k I := by sorry
