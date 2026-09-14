import Mathlib

set_option autoImplicit false



def pvals : List Nat :=
  [2, 3, 7, 5, 11, 7, 29, 17, 19, 11, 23, 13, 53, 29, 31, 17, 103, 19, 191, 41,
   43, 23, 47, 73, 101, 53, 109, 29, 59, 31]

def check : Bool :=
  pvals.length == 30 &&
  (List.range 30).all fun i =>
    let n : Nat := i + 1
    let p : Nat := pvals[i]!
    Nat.Prime p && p % n == 1

theorem msl_fmz_erdos456_campaign_001_R008_L1_a1r3  : check = true := by decide

-- axiom footprint
#print axioms pvals
#print axioms check
#print axioms msl_fmz_erdos456_campaign_001_R008_L1_a1r3
