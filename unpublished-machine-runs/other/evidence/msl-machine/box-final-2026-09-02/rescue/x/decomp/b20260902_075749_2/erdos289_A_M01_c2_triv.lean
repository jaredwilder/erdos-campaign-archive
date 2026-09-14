import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset
open Filter

def Good (k : Nat) (I : Fin k → Nat × Nat) : Prop :=
  (∀ (i : Fin k), (I i).1 < (I i).2) ∧
  (∀ (i j : Fin k), i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1)

def sumQ (k : Nat) (I : Fin k → Nat × Nat) : Rat :=
  ∑ i : Fin k, ∑ n ∈ Icc (I i).1 (I i).2, ((n : Rat))⁻¹

def prepend23 (k : Nat) (T : Fin k → Nat × Nat) : Fin (k + 1) → Nat × Nat :=
  Fin.cons (2, 3) T

theorem msl_erdos289_a_m01_c2_triv (k : Nat) (T : Fin k → Nat × Nat) : sumQ (k + 1) (prepend23 k T) = ((1 : Rat) / 2 + (1 : Rat) / 3) + sumQ k T := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
