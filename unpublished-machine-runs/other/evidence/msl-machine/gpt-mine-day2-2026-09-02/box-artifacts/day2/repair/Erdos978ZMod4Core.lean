import Mathlib

set_option autoImplicit false

/-- Modular core: x^4+2 is never 0 modulo 4. -/
theorem erdos978_fourth_plus_two_ne_zero (x : ZMod 4) :
    x ^ 4 + 2 ≠ 0 := by
  decide +revert

-- axiom footprint
#print axioms erdos978_fourth_plus_two_ne_zero
