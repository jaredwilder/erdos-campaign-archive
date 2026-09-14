import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def GoodPair (p : Fin 2 → ℕ+ × ℕ+) : Prop :=
  ∀ j : Fin 2, (p j).1 ≤ (p j).2 ∧
    ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (p j).1 (p j).2, (nⱼ⁻¹ : ℚ)) = n
