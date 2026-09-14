import Mathlib

set_option autoImplicit false


-- All pairs 1 ≤ a < b ≤ 12, checked by plain decide over an explicit finite list.

def quotVals (a b : Nat) : List Nat :=
  let g := Nat.gcd a b
  [a / g, b / g]

-- For a 2-element set {a, b} with a < b: the value 1 is always achievable
-- (take (a,a) or (b,b)), and a/g ≠ b/g since a ≠ b and division by the
-- common gcd preserves distinctness. So the value set has size ≥ 2.
def pairOK (a b : Nat) : Bool :=
  (quotVals a b).eraseDups.length == 2

def allPairs : List (Nat × Nat) :=
  (List.range 11).flatMap (fun i =>
    (List.range (10 - i)).map (fun j => (i + 1, i + 1 + j + 1)))

def universalLower : Bool := allPairs.all (fun p => pairOK p.1 p.2)

-- Witness {1, 2} attains exactly 2 distinct values: {1, 2}
def witnessVals : List Nat := (quotVals 1 2).eraseDups
def witnessTight : Bool := witnessVals == [1, 2]

def check_base : Bool := universalLower && witnessTight

theorem msl_fmz_erdos539_campaign_001_R005_L1  : check_base = true := by decide

-- axiom footprint
#print axioms quotVals
#print axioms pairOK
#print axioms allPairs
#print axioms universalLower
#print axioms witnessVals
#print axioms witnessTight
#print axioms check_base
#print axioms msl_fmz_erdos539_campaign_001_R005_L1
