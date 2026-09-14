import Mathlib

set_option autoImplicit false


def isAP (a b c : Nat) : Bool := a + c = 2 * b
def apFree (s : List Nat) : Bool :=
  s.all (fun a => s.all (fun b => s.all (fun c => !(isAP a b c) || a == b || b == c || a == c)))
def checkPartition : Bool :=
  apFree [1,4,5,8] && apFree [2,3,6,7]

theorem msl_fmz_erdos197_campaign_001_R010_L1_a1r1  : checkPartition = true := by decide

-- axiom footprint
#print axioms isAP
#print axioms apFree
#print axioms checkPartition
#print axioms msl_fmz_erdos197_campaign_001_R010_L1_a1r1
