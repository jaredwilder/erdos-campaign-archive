import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset

def Admissible (k : Nat) : Prop :=
  ∃ (I : Fin k → Nat × Nat),
    (∀ (i : Fin k), (I i).1 < (I i).2) ∧
    (∀ (i j : Fin k), i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧
    (∀ (i : Fin k), 2 ≤ (I i).1) ∧
    (∑ i, ∑ n ∈ Icc (I i).1 (I i).2, ((n : Rat)⁻¹) = (1 : Rat))

theorem msl_erdos289_b_m01_c1_triv : ∀ (j : Nat), ¬ Admissible (2 * j + 3) := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
