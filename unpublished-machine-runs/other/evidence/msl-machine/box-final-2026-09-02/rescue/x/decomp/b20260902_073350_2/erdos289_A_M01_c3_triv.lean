import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset

open Finset

def SchemeOK (k : Nat) : Prop :=
  ∃ I : Fin k → Nat × Nat,
    (∀ i : Fin k, (I i).1 < (I i).2) ∧
    (∀ i j : Fin k, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧
    ∑ i : Fin k, ∑ n ∈ Finset.Icc (I i).1 (I i).2, ((n : Nat)⁻¹ : Rat) = 1

def ExtStep : Prop := ∀ (k : Nat), SchemeOK k → SchemeOK (k + 1)

def HasBase : Prop := ∃ (k0 : Nat), SchemeOK k0

def EventuallyScheme : Prop := ∃ (K : Nat), ∀ (k : Nat), K ≤ k → SchemeOK k

theorem msl_erdos289_a_m01_c3_triv : ExtStep → HasBase → EventuallyScheme := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
