import Mathlib

set_option autoImplicit false

/-- Modular core: a sum of two squares is never 3 modulo 4. -/
theorem erdos979_two_squares_ne_three (x y : ZMod 4) :
    x ^ 2 + y ^ 2 ≠ 3 := by
  decide +revert

-- axiom footprint
#print axioms erdos979_two_squares_ne_three
