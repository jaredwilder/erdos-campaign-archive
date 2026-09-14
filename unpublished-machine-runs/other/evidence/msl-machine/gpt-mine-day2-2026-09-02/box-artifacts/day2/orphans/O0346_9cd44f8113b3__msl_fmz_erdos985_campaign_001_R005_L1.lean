import Mathlib

set_option autoImplicit false


def mpow (m b : Nat) : Nat → Nat
  | 0 => 1 % m
  | e+1 => (b * mpow m b e) % m

def isCase (p : Nat) : Bool :=
  p >= 5 && mpow p 3 ((p-1)/2) != 1 % p

def check_L1 : Bool :=
  isCase 5 && isCase 17

theorem msl_fmz_erdos985_campaign_001_R005_L1  : check_L1 = true := by decide

-- axiom footprint
#print axioms mpow
#print axioms isCase
#print axioms check_L1
#print axioms msl_fmz_erdos985_campaign_001_R005_L1
