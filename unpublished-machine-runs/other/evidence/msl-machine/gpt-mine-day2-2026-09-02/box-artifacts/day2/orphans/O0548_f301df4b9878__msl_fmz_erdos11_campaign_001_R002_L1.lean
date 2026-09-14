import Mathlib

set_option autoImplicit false


def dividesNat (p k : Nat) : Bool := p * (k / p) == k

def squarefreeTD : Nat → Bool
  | 0 => false
  | 1 => true
  | k => ((List.range (k + 1)).filter (fun p => 2 ≤ p ∧ p ≤ k ∧ dividesNat p k)).all
           (fun p => ¬ dividesNat (p * p) k)

def decomposable (n : Nat) : Bool :=
  (List.range 11).any (fun l =>
    let p := 2 ^ l
    p ≤ n ∧ squarefreeTD (n - p))

def witnessTable : Bool :=
  decomposable 3 && decomposable 5 && decomposable 7 && decomposable 9 &&
  decomposable 11 && decomposable 13 && decomposable 15

theorem msl_fmz_erdos11_campaign_001_R002_L1  : witnessTable = true := by decide

-- axiom footprint
#print axioms dividesNat
#print axioms squarefreeTD
#print axioms decomposable
#print axioms witnessTable
#print axioms msl_fmz_erdos11_campaign_001_R002_L1
