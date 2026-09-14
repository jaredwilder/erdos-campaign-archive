import Mathlib

set_option autoImplicit false


theorem msl_cable_selftest_false  : 2 + 2 = 5 := by decide

-- axiom footprint
#print axioms msl_cable_selftest_false
