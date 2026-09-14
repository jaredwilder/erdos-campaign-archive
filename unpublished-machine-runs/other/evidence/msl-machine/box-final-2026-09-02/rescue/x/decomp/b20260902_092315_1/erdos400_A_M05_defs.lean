import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def gk (k n : Nat) : Int :=
  sSup {v : Int | ∃ a : Fin k → Nat, (∀ i : Fin k, 1 ≤ a i) ∧
    ((∏ i : Fin k, (a i).factorial) ∣ n.factorial) ∧
    v = (∑ i : Fin k, ((a i : Nat) : Int)) - (n : Int)}
