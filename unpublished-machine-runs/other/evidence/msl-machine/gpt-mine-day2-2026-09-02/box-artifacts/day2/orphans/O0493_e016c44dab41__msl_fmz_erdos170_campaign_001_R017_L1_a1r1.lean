import Mathlib

set_option autoImplicit false


def witness : List (List Nat) := [[0,1],[0,1,2],[0,1,3],[0,1,3,4],[0,1,3,5],[0,1,4,6],[0,1,3,4,7]]

def pairSums (a : List Nat) : List Nat :=
  (a.zipIdx.flatMap fun (x, i) =>
    (a.drop (i+1)).map (fun y => x + y)).eraseDups

def covers (a : List Nat) (N : Nat) : Bool :=
  (List.range (N+1)).all (fun t => pairSums a contains t)

def minK (N : Nat) : Nat :=
  -- smallest k with k*(k-1) >= 2*N  (ceil((1+sqrt(1+8N))/2))
  (List.range 50).find! (fun k => k*(k-1) >= 2*N)

def claimFN (N : Nat) (F : Nat) (w : List Nat) : Bool :=
  w.length == F
  && covers w N
  && minK N == F  -- k(k-1)>=2N lower bound is tight at F

def checkAll : Bool :=
  claimFN 1 2 [0,1]
  && claimFN 2 3 [0,1,2]
  && claimFN 3 3 [0,1,3]
  && claimFN 4 4 [0,1,3,4]
  && claimFN 5 4 [0,1,3,5]
  && claimFN 6 4 [0,1,4,6]
  && claimFN 7 5 [0,1,3,4,7]

theorem msl_fmz_erdos170_campaign_001_R017_L1_a1r1  : checkAll = true := by native_decide

-- axiom footprint
#print axioms witness
#print axioms pairSums
#print axioms covers
#print axioms minK
#print axioms claimFN
#print axioms checkAll
#print axioms msl_fmz_erdos170_campaign_001_R017_L1_a1r1
