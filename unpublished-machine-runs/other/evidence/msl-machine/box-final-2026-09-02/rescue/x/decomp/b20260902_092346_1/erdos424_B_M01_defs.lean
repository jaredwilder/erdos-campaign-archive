import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def genNext (s : Finset Nat) : Finset Nat :=
  s ∪ Finset.image (fun p : Nat × Nat => p.1 * p.2 - 1)
      (Finset.filter (fun p : Nat × Nat => p.1 ≠ p.2) (s ×ˢ s))

def genSeq : Nat → Finset Nat
  | 0 => {2, 3}
  | (n + 1) => genNext (genSeq n)

def generatedSet : Set Nat := ⋃ (n : Nat), (genSeq n : Set Nat)

def countIn (S : Set Nat) (n : Nat) : Nat :=
  (Finset.filter (fun m : Nat => m ∈ S) (Finset.Icc 1 n)).card

def HasPosDensity (S : Set Nat) : Prop :=
  ∃ (c : Q), 0 < c ∧ ∃ (N : Nat), ∀ (n : Nat), N ≤ n → (c : Q) * (n : Q) ≤ (countIn S n : Q)
