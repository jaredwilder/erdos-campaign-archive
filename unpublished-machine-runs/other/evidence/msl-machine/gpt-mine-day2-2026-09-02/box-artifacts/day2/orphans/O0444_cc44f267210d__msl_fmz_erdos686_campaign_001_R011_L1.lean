import Mathlib

set_option autoImplicit false


def isHexChar (c : Char) : Bool :=
  ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')

def checkHex16 (s : String) : Bool :=
  s.length == 16 ∧ s.data.all isHexChar

def contractSha : String := "db38b9842513b366"

def check : Bool := checkHex16 contractSha

theorem msl_fmz_erdos686_campaign_001_R011_L1  : check = true := by decide

-- axiom footprint
#print axioms isHexChar
#print axioms checkHex16
#print axioms contractSha
#print axioms check
#print axioms msl_fmz_erdos686_campaign_001_R011_L1
