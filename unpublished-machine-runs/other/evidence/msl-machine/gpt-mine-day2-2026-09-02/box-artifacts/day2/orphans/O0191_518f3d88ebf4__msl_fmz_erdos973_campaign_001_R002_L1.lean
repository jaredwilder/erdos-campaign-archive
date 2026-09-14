import Mathlib

set_option autoImplicit false


def check_sqrt2_interval : Bool :=
  (1414213^2 < 2000000000000) && (2000000000000 < 1414214^2)
-- Exact Nat arithmetic: with 10^6 denominators on both sides of the strict
-- inequality 1414213/10^6 < √2 < 1414214/10^6, cross-multiplication by 10^12
-- (a positive integer) preserves strict inequality, so the rational interval
-- claim is equivalent to the two integer inequalities above. No floats, no
-- tolerance, no Classical choice: the Bool expression is total and computable.

theorem msl_fmz_erdos973_campaign_001_R002_L1  : check_sqrt2_interval = true := by decide

-- axiom footprint
#print axioms check_sqrt2_interval
#print axioms msl_fmz_erdos973_campaign_001_R002_L1
