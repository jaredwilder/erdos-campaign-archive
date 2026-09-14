import Mathlib

set_option autoImplicit false


def A : List Nat := [1, 2, 4, 8, 16]
def pairSums : List Nat := A.flatMap (fun a => A.map (fun b => a + b))
def cnt (n : Nat) : Nat := (pairSums.filter (fun s => s = n)).length
def ns : List Nat := List.range 33
def sidon : Bool := ns.all (fun n => cnt n <= 2)
def sumSq : Nat := ns.foldl (fun s n => s + cnt n * cnt n) 0
def check : Bool := sidon && (sumSq == 25) && (pairSums.length == 25)

theorem msl_fmz_erdos1192_campaign_001_R009_L1  : check = true := by native_decide

-- axiom footprint
#print axioms A
#print axioms pairSums
#print axioms cnt
#print axioms ns
#print axioms sidon
#print axioms sumSq
#print axioms check
#print axioms msl_fmz_erdos1192_campaign_001_R009_L1
