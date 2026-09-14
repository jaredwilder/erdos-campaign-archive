import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
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

theorem msl_erdos288_lem_r003_l1_composition : ((∀ (a b : ℕ+) (k : ℕ+), a ≤ b → (∑ n ∈ Set.Icc a b, (n⁻¹ : ℚ)) = (k : ℚ) → a = 1 ∧ b = 1 ∧ k = 1) ∧ (Set.Finite SinglePairs) ∧ (Set.Finite ProperPairs)) → (Set.Finite { I : Fin 2 → ℕ+ × ℕ+ | IsGood I }) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos288_lem_r003_l1_composition
