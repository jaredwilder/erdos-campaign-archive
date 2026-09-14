import Mathlib

set_option autoImplicit false


def checkRange : List Int := [(-7), (-2), 0, 1, 3, 100]

def p2_nonneg_ok : Bool :=
  checkRange.all (fun p => p * p >= 0)

def q2_pos_ok : Bool :=
  checkRange.all (fun q => q = 0 || q * q > 0)

def x2_eq0_iff_p0_ok : Bool :=
  checkRange.all (fun p =>
    checkRange.all (fun q =>
      q = 0 || ((p * q) * (p * q) >= 0 ∧ (((p * q) * (p * q) = 0) ↔ p = 0))))

def L1_check : Bool := p2_nonneg_ok && q2_pos_ok && x2_eq0_iff_p0_ok

theorem msl_fmz_erdos978_campaign_001_R001_L1  : L1_check = true := by decide

-- axiom footprint
#print axioms checkRange
#print axioms p2_nonneg_ok
#print axioms q2_pos_ok
#print axioms x2_eq0_iff_p0_ok
#print axioms L1_check
#print axioms msl_fmz_erdos978_campaign_001_R001_L1
