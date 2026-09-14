import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def p (n : Nat) : Nat := (Nat.partitions n).card

def F (n : Nat) : Nat :=
  (Nat.factors ((Finset.Icc 1 n).fold (fun (acc : Nat) (k : Nat) => acc * p k) 1)).toFinset.card
