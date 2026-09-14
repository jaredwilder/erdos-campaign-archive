import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset

def NoDecomp (k : Nat) : Prop :=
  ¬ ∃ I : Fin k → Nat × Nat,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧
    ∑ i, ∑ n ∈ Finset.Icc (I i).1 (I i).2, ((n : Nat)⁻¹ : Rat) = 1

theorem msl_erdos289_b_m01_c1_triv : NoDecomp 1 := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
