import Mathlib

set_option autoImplicit false


def bits (n k : Nat) : Bool := (n >>> k) % 2 == 1
def threeAPs : List (Nat × Nat × Nat) :=
  (List.range 7).map (fun a => (a, a+1, a+2)) ++
  (List.range 5).map (fun a => (a, a+2, a+4)) ++
  (List.range 3).map (fun a => (a, a+3, a+6)) ++
  [(0,4,8)]
def monoAt (n : Nat) (t : Nat × Nat × Nat) : Bool :=
  (bits n t.1 && bits n t.2.1 && bits n t.2.2) ||
  (!(bits n t.1) && !(bits n t.2.1) && !(bits n t.2.2))
def coloringClean (n : Nat) : Bool := !(threeAPs.any (monoAt n))
def aps8 : List (Nat × Nat × Nat) :=
  (List.range 6).map (fun a => (a, a+1, a+2)) ++
  (List.range 4).map (fun a => (a, a+2, a+4)) ++
  (List.range 2).map (fun a => (a, a+3, a+6))
def witnessRBRBBRBR : Nat := 0b10100101
def checkWitness : Bool := !(aps8.any (monoAt witnessRBRBBRBR))
def exhaustiveNoClean9 : Bool :=
  (List.range 512).all (fun n => !(coloringClean n))
def checkW23 : Bool := checkWitness && exhaustiveNoClean9

theorem msl_fmz_erdos197_campaign_001_R004_L1_a3r1  : checkW23 = true := by decide

-- axiom footprint
#print axioms bits
#print axioms threeAPs
#print axioms monoAt
#print axioms coloringClean
#print axioms aps8
#print axioms witnessRBRBBRBR
#print axioms checkWitness
#print axioms exhaustiveNoClean9
#print axioms checkW23
#print axioms msl_fmz_erdos197_campaign_001_R004_L1_a3r1
