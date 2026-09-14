import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def TripleFree (s : Finset Nat) : Prop :=
  ∀ n : Nat, n ∈ s → 2 * n ∈ s → 3 * n ∈ s → False

def F (N : Nat) : Nat :=
  ((Finset.univ.filter fun s : Finset Nat => s ⊆ Finset.Icc 1 N ∧ TripleFree s).sup Finset.card)
