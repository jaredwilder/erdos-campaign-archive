import Mathlib

set_option autoImplicit false


def inA (a : Nat) : Bool := (a % 2 == 0) || (a % 3 == 0)
def Bset (N : Nat) : List Nat := (List.range (N+1)).filter (fun n => n > 0 && !inA n)
def gapPairs (N : Nat) : List (Nat × Nat) :=
  let b := Bset N
  b.zip (b.drop 1)
def gapCheck (N : Nat) : Bool :=
  (gapPairs N).all (fun p =>
    match p with
    | (x, y) => let d := y - x
                (d == 2 || d == 4) && ((d == 4 && x % 6 == 1) || (d == 2 && x % 6 == 5)))
def residueCheck (N : Nat) : Bool :=
  (Bset N).all (fun n => n % 6 == 1 || n % 6 == 5)
def checkA23 : Bool := residueCheck 120 && gapCheck 120

theorem msl_fmz_erdos489_campaign_001_R002_L1  : checkA23 = true := by decide

-- axiom footprint
#print axioms inA
#print axioms Bset
#print axioms gapPairs
#print axioms gapCheck
#print axioms residueCheck
#print axioms checkA23
#print axioms msl_fmz_erdos489_campaign_001_R002_L1
