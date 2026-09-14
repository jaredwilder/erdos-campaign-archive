import Mathlib

set_option autoImplicit false


def w1 : List Nat := [0,1]
def w2 : List Nat := [0,1,2]
def w3 : List Nat := [0,1,3]
def w4 : List Nat := [0,1,3,4]
def w5 : List Nat := [0,1,3,5]
def w6 : List Nat := [0,1,4,6]
def w7 : List Nat := [0,1,3,4,7]

def sumsCover (a : List Nat) (N : Nat) : Bool :=
  (List.range (N+1)).all (fun t =>
    (a.flatMap (fun x => a.map (fun y => x + y))).contains t)

def lowerK (N : Nat) : Nat :=
  (List.range 60).filter (fun k => k * (k-1) >= 2*N) |>.head!

def claimFN (N : Nat) (F : Nat) (w : List Nat) : Bool :=
  w.length == F && sumsCover w N && lowerK N == F

def checkAll : Bool :=
  claimFN 1 2 w1 && claimFN 2 3 w2 && claimFN 3 3 w3
  && claimFN 4 4 w4 && claimFN 5 4 w5 && claimFN 6 4 w6
  && claimFN 7 5 w7

theorem msl_fmz_erdos170_campaign_001_R017_L1_a1r2  : checkAll = true := by native_decide

-- axiom footprint
#print axioms w1
#print axioms w2
#print axioms w3
#print axioms w4
#print axioms w5
#print axioms w6
#print axioms w7
#print axioms sumsCover
#print axioms lowerK
#print axioms claimFN
#print axioms checkAll
#print axioms msl_fmz_erdos170_campaign_001_R017_L1_a1r2
