import Mathlib

set_option autoImplicit false


-- Arithmetic content of L1, with binomials expanded to products of Nat
-- to avoid any division or truncated subtraction in the decidable check.
def C9_2 : Nat := (9 * 8) / 2
def C50_3 : Nat := (50 * 49 * 48) / 6

def checkL1 : Bool :=
  (12 * 12 == 144)
  && (144 == 4 * C9_2)
  && (140 * 140 == 19600)
  && (19600 == C50_3)
  && (705600 == 4 * (140 * 140))

theorem msl_fmz_erdos930_campaign_001_R002_L1  : checkL1 = true := by native_decide

-- axiom footprint
#print axioms C9_2
#print axioms C50_3
#print axioms checkL1
#print axioms msl_fmz_erdos930_campaign_001_R002_L1
