import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def certPassed (b : Bool) : Prop := b = true

def verifierRefutes (P : Prop) [inst : Decidable P] : Prop := decide P = false

theorem msl_erdos18_lem_r004_l1_c2_triv (P : Prop) (inst : Decidable P) : certPassed (decide P) → decide P = true := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
