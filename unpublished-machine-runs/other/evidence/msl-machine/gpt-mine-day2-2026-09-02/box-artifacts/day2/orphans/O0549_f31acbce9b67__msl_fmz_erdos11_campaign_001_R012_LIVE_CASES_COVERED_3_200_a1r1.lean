import Mathlib

set_option autoImplicit false


def Nat.sqfree : Nat -> Bool
  | 0 => false
  | 1 => true
  | n => (List.range (n+1)).all (fun d => d*d != 0 && (d*d ∣ n) -> !((d*d)*(d*d) ∣ n) || d*d == 1) -- replaced below by exact def
def squarefree (n : Nat) : Bool :=
  n != 0 && (List.range (n+2)).all (fun d => !(d*d ∣ n) || d == 1)
def isPow2 (n : Nat) : Bool := n != 0 && (n &&& (n-1)) == 0
def hasWitness (n : Nat) : Bool :=
  (List.range (Nat.log2 n + 1)).any (fun l => isPow2 (2^l) && n > 2^l && squarefree (n - 2^l))
def checkRange : Bool :=
  (List.range 99).all (fun i =>
    let n := 2*i + 3
    if squarefree (n-1) then true else hasWitness n)
def maxLrecord : Nat :=
  (List.range 99).foldl (fun acc i =>
    let n := 2*i + 3
    if squarefree (n-1) then acc else
      acc.max ((List.range (Nat.log2 n + 1)).filter (fun l => n > 2^l && squarefree (n - 2^l)).foldl max 0)) 0

theorem msl_fmz_erdos11_campaign_001_R012_LIVE_CASES_COVERED_3_200_a1r1  : checkRange = true := by native_decide

-- axiom footprint
#print axioms Nat.sqfree
#print axioms squarefree
#print axioms isPow2
#print axioms hasWitness
#print axioms checkRange
#print axioms maxLrecord
#print axioms msl_fmz_erdos11_campaign_001_R012_LIVE_CASES_COVERED_3_200_a1r1
