import Mathlib

set_option autoImplicit false


def closer_selftest_check (bound : Nat) : Bool :=
  (List.range bound).all (fun n => n + 0 == n)

theorem msl_closer_selftest_kernel  : closer_selftest_check 8 = true := by decide

-- axiom footprint
#print axioms closer_selftest_check
#print axioms msl_closer_selftest_kernel
