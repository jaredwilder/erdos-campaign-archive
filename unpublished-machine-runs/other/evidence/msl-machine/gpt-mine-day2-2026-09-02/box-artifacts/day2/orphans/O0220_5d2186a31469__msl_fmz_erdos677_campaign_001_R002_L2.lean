import Mathlib

set_option autoImplicit false


def injCheck (N : Nat) : Bool :=
  (List.range N).all fun n =>
    (List.range N).all fun m => n = m ∨ ¬((n + 1 : Nat) = m + 1)
-- M(n,1) = n+1 by definition of lcm of the single-element interval {n+1};
-- injCheck N decides injectivity of n ↦ M(n,1) on the finite range n,m < N.

theorem msl_fmz_erdos677_campaign_001_R002_L2  : injCheck 64 = true := by decide

-- axiom footprint
#print axioms injCheck
#print axioms msl_fmz_erdos677_campaign_001_R002_L2
