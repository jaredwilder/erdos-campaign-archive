import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset

def v2 (n : Nat) : Nat := n.factorization 2

def maxV2 (a b : Nat) : Nat := Finset.sup (Icc a b) v2

def Admissible (k : Nat) (I : Fin k → Nat × Nat) : Prop :=
  (∀ i : Fin k, (I i).1 < (I i).2) ∧
  (∀ i j : Fin k, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1)

def gMaxV2 (k : Nat) (I : Fin k → Nat × Nat) : Nat :=
  Finset.sup (Finset.univ : Finset (Fin k)) (fun i => maxV2 (I i).1 (I i).2)

def maxAttain (k : Nat) (I : Fin k → Nat × Nat) : Nat :=
  (Finset.univ.filter (fun i : Fin k => maxV2 (I i).1 (I i).2 = gMaxV2 k I)).card

theorem msl_erdos289_b_m01_c5_triv (m : Nat) (q : Rat) : 1 ≤ m → Rat.num ((2 : Nat)^m * q) % 2 = 1 → q ≠ 1 := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
