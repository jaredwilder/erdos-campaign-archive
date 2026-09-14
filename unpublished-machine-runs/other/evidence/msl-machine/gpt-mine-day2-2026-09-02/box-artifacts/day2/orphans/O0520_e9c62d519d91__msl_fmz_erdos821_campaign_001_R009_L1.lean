import Mathlib

set_option autoImplicit false


def phi : Nat → Nat
  | 0 => 0
  | (m+1) => (List.range (m+2)).filter (fun k => Nat.gcd k (m+1) == 1) |>.length

def gCnt (n : Nat) : Nat :=
  (List.range 8193).filter (fun m => phi m == n) |>.length

def anchors : Bool :=
  gCnt 24 == 10 && gCnt 36 == 13 && gCnt 60 == 20

def smallRange : Bool :=
  (List.range 9).all (fun n => gCnt n ==
    (List.range 65).filter (fun m => phi m == n) |>.length)

def closureCheck : Bool := anchors && smallRange

theorem msl_fmz_erdos821_campaign_001_R009_L1  : closureCheck = true := by native_decide

-- axiom footprint
#print axioms phi
#print axioms gCnt
#print axioms anchors
#print axioms smallRange
#print axioms closureCheck
#print axioms msl_fmz_erdos821_campaign_001_R009_L1
