import Mathlib

set_option autoImplicit false


def check_cert : Bool :=
  decide ((15 : Nat) > 8) &&
  decide ((51 : Nat) > 32) &&
  decide ((69 : Nat) > 44) &&
  decide ((69 : Rat) / 44 - 3 / 2 = 3 / 44) &&
  decide ((69 : Rat) / 44 - 3 / 2 > 0)

theorem msl_fmz_erdos51_campaign_001_R007_L1  : check_cert = true := by decide

-- axiom footprint
#print axioms check_cert
#print axioms msl_fmz_erdos51_campaign_001_R007_L1
