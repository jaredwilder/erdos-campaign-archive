import Mathlib

set_option autoImplicit false


def witness : List Nat := [2, 4, 8, 16, 32, 64]
def isWitness (n : Nat) : Bool := (2 ^ n) % n == 0
def check : Bool := witness.all isWitness

theorem msl_fmz_erdos479_campaign_001_R003_L1  : check = true := by decide

-- axiom footprint
#print axioms witness
#print axioms isWitness
#print axioms check
#print axioms msl_fmz_erdos479_campaign_001_R003_L1
