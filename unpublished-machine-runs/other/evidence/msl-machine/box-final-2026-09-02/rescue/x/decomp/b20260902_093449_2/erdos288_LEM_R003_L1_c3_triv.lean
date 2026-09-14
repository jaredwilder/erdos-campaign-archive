import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def harmonicSum (I : Fin 2 → ℕ+ × ℕ+) : ℚ :=
  ∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)

def IsGood (I : Fin 2 → ℕ+ × ℕ+) : Prop :=
  (∀ j : Fin 2, (I j).1 ≤ (I j).2) ∧ ∃ n : ℕ+, harmonicSum I = (n : ℚ)

def SinglePairs : Set (Fin 2 → ℕ+ × ℕ+) :=
  {I | IsGood I ∧ ∃ j : Fin 2, (I j).1 = (I j).2}

def ProperPairs : Set (Fin 2 → ℕ+ × ℕ+) :=
  {I | IsGood I ∧ ∀ j : Fin 2, (I j).1 < (I j).2}

theorem msl_erdos288_lem_r003_l1_c3_triv : Set.Finite ProperPairs := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
