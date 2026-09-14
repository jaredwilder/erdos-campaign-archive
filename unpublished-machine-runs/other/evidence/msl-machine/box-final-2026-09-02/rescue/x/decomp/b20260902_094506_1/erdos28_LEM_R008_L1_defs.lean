import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def reps (A : Set Nat) (n : Nat) : Nat :=
  ((Finset.Icc (0 : Nat) n).filter (fun (a : Nat) => a ∈ A ∧ (n - a) ∈ A)).card
