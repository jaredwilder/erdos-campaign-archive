import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def oddPart (n : Nat) : Nat := n / 2 ^ (n.factorization 2)
