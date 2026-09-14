import Mathlib

set_option autoImplicit false



def isSquarefree (n : Nat) : Bool :=
  1 ≤ n ∧ ((List.range (n+1)).filter
    (fun d => 2 ≤ d ∧ d * d ∣ n)).isEmpty

def existsSquarefreeSum (n : Nat) : Bool :=
  (List.range 25).any fun l =>
    let p := 2 ^ l
    1 ≤ n - p ∧ n - p + p = n ∧ isSquarefree (n - p)

def oddCandidates : List Nat :=
  (List.range 100).filter (fun n => 1 < n ∧ n % 2 = 1)

def allOddCovered : Bool :=
  (oddCandidates.map existsSquarefreeSum).all id

def hardWitnesses : List (Nat × Nat × Nat) :=
  [(29,13,4),(53,37,4),(89,73,4),(95,79,4),(97,89,3)]

def checkHard : Bool :=
  (hardWitnesses.map
    (fun (n,k,l) =>
      1 < n ∧ n % 2 = 1 ∧ 1 ≤ k ∧ 3 ≤ l ∧ l ≤ 4
        ∧ isSquarefree k ∧ k + 2 ^ l = n)).all id

def checkL1 : Bool := allOddCovered ∧ checkHard

theorem msl_fmz_erdos11_campaign_001_R005_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms isSquarefree
#print axioms existsSquarefreeSum
#print axioms oddCandidates
#print axioms allOddCovered
#print axioms hardWitnesses
#print axioms checkHard
#print axioms checkL1
#print axioms msl_fmz_erdos11_campaign_001_R005_L1
