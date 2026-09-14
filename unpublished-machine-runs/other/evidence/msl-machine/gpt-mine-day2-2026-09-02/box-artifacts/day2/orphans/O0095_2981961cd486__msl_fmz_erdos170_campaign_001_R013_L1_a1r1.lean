import Mathlib

set_option autoImplicit false


def U : List Nat := List.range 8
def covers (A : List Nat) : Bool := (List.range 8).all (fun d => A.any (fun a => A.any (fun b => a - b = d || b - a = d)))
def subsets : List (List Nat) := U.foldl (fun acc n => acc ++ acc.map (fun s => n :: s)) [[]]
def minCoverSize : Nat := (subsets.filter covers).foldl (fun m s => min m s.length) 8
def check : Bool := minCoverSize == 5 && covers [0,1,2,4,7]

theorem msl_fmz_erdos170_campaign_001_R013_L1_a1r1  : check = true := by decide

-- axiom footprint
#print axioms U
#print axioms covers
#print axioms subsets
#print axioms minCoverSize
#print axioms check
#print axioms msl_fmz_erdos170_campaign_001_R013_L1_a1r1
