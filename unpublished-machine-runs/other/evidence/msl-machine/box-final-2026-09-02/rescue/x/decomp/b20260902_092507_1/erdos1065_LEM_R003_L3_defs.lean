import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def IsTwoPowQ (p k q : Nat) : Prop := p.Prime ∧ q.Prime ∧ p = 2 ^ k * q + 1

def CompleteRows (S : Finset Nat) : Prop :=
  ∀ (k : Nat), (∃ (p q : Nat), p ≤ 200 ∧ q ≤ 100 ∧ IsTwoPowQ p k q) → k ∈ S
