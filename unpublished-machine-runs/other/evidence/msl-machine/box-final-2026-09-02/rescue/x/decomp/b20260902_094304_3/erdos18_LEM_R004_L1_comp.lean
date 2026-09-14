import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def certPassed (b : Bool) : Prop := b = true

def verifierRefutes (P : Prop) [inst : Decidable P] : Prop := decide P = false

theorem msl_erdos18_lem_r004_l1_composition (P : Prop) (inst : Decidable P) : ((decide P = true ∨ verifierRefutes P) ∧ (certPassed (decide P) → decide P = true)) → (verifierRefutes P → ¬ certPassed (decide P)) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos18_lem_r004_l1_composition
