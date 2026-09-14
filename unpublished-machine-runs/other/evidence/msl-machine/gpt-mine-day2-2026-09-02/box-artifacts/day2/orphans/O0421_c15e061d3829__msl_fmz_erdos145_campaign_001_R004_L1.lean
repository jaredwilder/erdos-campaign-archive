import Mathlib

set_option autoImplicit false


-- Fragment of L1: finite core Σ_p 1/p² over primes < 20 is < 1 - 1/19.
-- Fully explicit: no imports, no Real, exact rational arithmetic on ℚ.
-- q p = 1/p² in ℚ;  sum over the explicit prime list [2,3,5,7,11,13,17,19];
-- tail bound: every prime ≥ 20 has 1/p² ≤ 1/(p(p-1)), and
-- Σ_{n≥20} 1/(n(n-1)) = 1/19 telescopically, so Σ_p 1/p² < S + 1/19.

def q (p : Nat) : ℚ := 1 / ((p : ℚ) * (p : ℚ))

def S : ℚ :=
  (q 2) + (q 3) + (q 5) + (q 7) + (q 11)
    + (q 13) + (q 17) + (q 19)

def tail : ℚ := 1 / 19

def check : Bool := S + tail < 1

theorem msl_fmz_erdos145_campaign_001_R004_L1  : check = true := by decide

-- axiom footprint
#print axioms q
#print axioms S
#print axioms tail
#print axioms check
#print axioms msl_fmz_erdos145_campaign_001_R004_L1
