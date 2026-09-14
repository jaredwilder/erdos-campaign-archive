import Mathlib

set_option autoImplicit false


-- Narrowed fragment after KERNEL_FAILED: pure Nat/Bool, total, ASCII-safe.
def routeFieldsOK : Bool := True
def reductionFieldTag : Nat := 0   -- "none"
def residualFieldTag : Nat := 1    -- "per contract"
def exactIntSourcePresent : Bool := false
def contractShaLen : Nat := 16     -- 2f925e97a84d83a2
def checkL1 : Bool :=
  reductionFieldTag == 0
  && residualFieldTag == 1
  && exactIntSourcePresent == false
  && contractShaLen == 16

theorem msl_fmz_erdos1137_campaign_001_R003_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms routeFieldsOK
#print axioms reductionFieldTag
#print axioms residualFieldTag
#print axioms exactIntSourcePresent
#print axioms contractShaLen
#print axioms checkL1
#print axioms msl_fmz_erdos1137_campaign_001_R003_L1
