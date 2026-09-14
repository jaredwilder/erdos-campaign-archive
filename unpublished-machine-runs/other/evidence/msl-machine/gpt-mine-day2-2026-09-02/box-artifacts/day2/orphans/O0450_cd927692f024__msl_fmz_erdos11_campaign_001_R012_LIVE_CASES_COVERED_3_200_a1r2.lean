import Mathlib

set_option autoImplicit false


def squarefree (n : Nat) : Bool :=
  n != 0 && (List.range (n + 1)).all (fun d => d < 2 || n % (d * d) != 0)

def hasWitness (n : Nat) : Bool :=
  (List.range (Nat.log2 n + 1)).any
    (fun l => squarefree (n - 2 ^ (l + 1)))

def checkRange : Bool :=
  (List.range 99).all (fun i =>
    let n := 2 * i + 3
    squarefree (n - 1) || hasWitness n)

def maxL : Nat :=
  (List.range 99).foldl (fun acc i =>
    let n := 2 * i + 3
    if squarefree (n - 1) then acc
    else (List.range (Nat.log2 n + 1)).filter
           (fun l => squarefree (n - 2 ^ (l + 1)))
           |>.foldl (fun a l => max a (l + 1)) acc) 0

def checkAll : Bool := checkRange && maxL > 0

theorem msl_fmz_erdos11_campaign_001_R012_LIVE_CASES_COVERED_3_200_a1r2  : checkAll = true := by native_decide

-- axiom footprint
#print axioms squarefree
#print axioms hasWitness
#print axioms checkRange
#print axioms maxL
#print axioms checkAll
#print axioms msl_fmz_erdos11_campaign_001_R012_LIVE_CASES_COVERED_3_200_a1r2
