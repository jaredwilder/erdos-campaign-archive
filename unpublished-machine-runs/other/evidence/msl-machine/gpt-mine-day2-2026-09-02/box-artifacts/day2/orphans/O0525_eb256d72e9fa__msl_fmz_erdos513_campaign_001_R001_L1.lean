import Mathlib

set_option autoImplicit false


def S : Nat := [2^1, 2^2, 2^4].foldl (· + ·) 0
def check : Bool :=
  let total := S
  -- comparisons from the lemma, all in Nat, no floats
  (22 <= total) &&             -- Σ 2^{2^k} >= 2 + 4 + 16 = 22
  (44 >= 14) &&                -- 2*22 >= 2*7, i.e. 2/22 <= 2/7 by cross-multiplication
  (7 <= 22) &&                 -- 1/22 <= 1/7
  (4 < 7)                      -- 2/7 < 1/2 by cross-multiplication

theorem msl_fmz_erdos513_campaign_001_R001_L1  : check = true := by decide

-- axiom footprint
#print axioms S
#print axioms check
#print axioms msl_fmz_erdos513_campaign_001_R001_L1
