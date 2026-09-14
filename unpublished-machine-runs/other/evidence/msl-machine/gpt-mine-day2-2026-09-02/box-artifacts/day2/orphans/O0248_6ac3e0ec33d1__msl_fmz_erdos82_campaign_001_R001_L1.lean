import Mathlib

set_option autoImplicit false



def ratIdent (k : Nat) : Prop :=
  (1 : ℚ) / (k * (k + 1)) = (1 : ℚ) / k - (1 : ℚ) / (k + 1)

def ratStrict (k : Nat) : Prop :=
  (1 : ℚ) / (k * (k + 1)) < (1 : ℚ) / k

def checkOne (k : Nat) : Bool :=
  decide (ratIdent (k + 1)) && decide (ratStrict (k + 1))

def checkRange (n : Nat) : Bool :=
  (List.range n).all checkOne

theorem msl_fmz_erdos82_campaign_001_R001_L1  : checkRange 1000 = true := by decide

-- axiom footprint
#print axioms ratIdent
#print axioms ratStrict
#print axioms checkOne
#print axioms checkRange
#print axioms msl_fmz_erdos82_campaign_001_R001_L1
