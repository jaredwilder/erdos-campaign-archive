import Mathlib

set_option autoImplicit false

namespace Day2Wrap


def Sub := List (List Nat)

def hereditary (F : Sub) : Bool :=
  F.all (fun A => (F.filter (fun B => B.all (fun x => A.contains x))) == [B | B <- F])

def intersecting (F : Sub) : Bool :=
  F.all (fun A => F.all (fun B => A.any (fun x => B.contains x)))

def maxIntersectingSub (F : Sub) : Nat :=
  let rec go : Sub -> List Sub -> Nat
    | [], _ => 0
    | (A :: rest), acc =>
      Nat.max (if intersecting (A :: acc) then 1 + go rest (A :: acc) else go rest acc)
              (go rest acc)
  go F []

def maxStar (F : Sub) (x : Nat) : Nat :=
  (F.filter (fun A => A.contains x)).length

def starBoundHolds (F : Sub) (x : Nat) : Bool :=
  maxIntersectingSub F <= maxStar F x

-- Enumeration of all hereditary families on X = {1,2} (the 4-set lattice subfamilies)
def allSubsetsOf2 : List (List Nat) := [[], [1], [2], [1,2]]

def subfamilies : List Sub :=
  allSubsetsOf2.filterM (fun _ => [true, false])

def emptyFam : Sub := [[]]

def checkVacuous : Bool :=
  hereditary emptyFam && !(intersecting emptyFam) && starBoundHolds emptyFam 1

def checkTwoChain : Bool :=
  let F : Sub := [[], [1]]
  hereditary F && !(intersecting F) && starBoundHolds F 1 && starBoundHolds F 2

def checkLattice : Bool :=
  let F : Sub := [[], [1], [2], [1,2]]
  hereditary F && !(intersecting F) && starBoundHolds F 1 && starBoundHolds F 2

-- Enumerate every subfamily of the 4-set lattice; for those that are hereditary,
-- the star bound must hold for some x in {1,2} (existential form of the contract).
def checkAll : Bool :=
  subfamilies.all (fun F =>
    if hereditary F then (starBoundHolds F 1 || starBoundHolds F 2) else true)

def check_core : Bool :=
  checkVacuous && checkTwoChain && checkLattice && checkAll

theorem msl_fmz_erdos701_campaign_001_R008_L1_a1r1  : check_core = true := by decide

end Day2Wrap
-- axiom footprint
#print axioms Day2Wrap.Sub
#print axioms Day2Wrap.hereditary
#print axioms Day2Wrap.intersecting
#print axioms Day2Wrap.maxIntersectingSub
#print axioms Day2Wrap.maxStar
#print axioms Day2Wrap.starBoundHolds
#print axioms Day2Wrap.allSubsetsOf2
#print axioms Day2Wrap.subfamilies
#print axioms Day2Wrap.emptyFam
#print axioms Day2Wrap.checkVacuous
#print axioms Day2Wrap.checkTwoChain
#print axioms Day2Wrap.checkLattice
#print axioms Day2Wrap.checkAll
#print axioms Day2Wrap.check_core
#print axioms Day2Wrap.msl_fmz_erdos701_campaign_001_R008_L1_a1r1
