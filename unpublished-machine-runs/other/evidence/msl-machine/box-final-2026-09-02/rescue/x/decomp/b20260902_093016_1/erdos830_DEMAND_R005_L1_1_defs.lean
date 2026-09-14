import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def sigmaTrial (n : Nat) : Nat :=
  (Finset.filter (fun (d : Nat) => d ∣ n) (Finset.Icc (1 : Nat) n)).sum (fun (d : Nat) => d)
