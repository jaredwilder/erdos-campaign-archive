import Mathlib

set_option autoImplicit false


def divCount : Nat → Nat → Nat
  | _, 0 => 0
  | m, d+1 => (if m % (d+1) == 0 then 1 else 0) + divCount m d

def tau (m : Nat) : Nat := divCount m m

def checkBound (m : Nat) : Bool := tau m * tau m <= 4 * m

def checkRange (lo hi : Nat) : Bool :=
  match lo with
  | 0 => checkBound 0
  | lo+1 => checkBound (lo+1) && (if lo+1 < hi then checkRange (lo+2) hi else true)

theorem msl_fmz_erdos826_campaign_001_R001_L1  : checkRange 1 32 = true := by decide

-- axiom footprint
#print axioms divCount
#print axioms tau
#print axioms checkBound
#print axioms checkRange
#print axioms msl_fmz_erdos826_campaign_001_R001_L1
