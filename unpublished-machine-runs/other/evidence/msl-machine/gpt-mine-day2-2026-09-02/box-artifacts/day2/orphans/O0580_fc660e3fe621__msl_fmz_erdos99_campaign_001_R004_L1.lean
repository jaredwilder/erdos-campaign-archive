import Mathlib

set_option autoImplicit false


-- Unit-square configuration {(0,0),(1,0),(0,1),(1,1)}, distances squared,
-- exact Nat arithmetic, avoiding any dependence on notation outside Lean core.

-- The six pairwise squared distances, listed explicitly:
def sqDists : List Nat := [1, 1, 2, 2, 1, 1]

def minDistIsOne : Bool :=
  (sqDists.all (fun d => d >= 1)) && (sqDists.any (fun d => d == 1))

def diamSqIsTwo : Bool :=
  (sqDists.all (fun d => d <= 2)) && (sqDists.any (fun d => d == 2))

-- The four 3-subsets' squared-distance triples:
def triples : List (List Nat) :=
  [ [1, 1, 2], [1, 2, 1], [2, 1, 1], [1, 2, 1] ]

def noUnitEquilateralTriple : Bool :=
  triples.all (fun t => !(t.all (fun d => d == 1)))

def check_unit_square_witness : Bool :=
  minDistIsOne && diamSqIsTwo && noUnitEquilateralTriple

theorem msl_fmz_erdos99_campaign_001_R004_L1  : check_unit_square_witness = true := by decide

-- axiom footprint
#print axioms sqDists
#print axioms minDistIsOne
#print axioms diamSqIsTwo
#print axioms triples
#print axioms noUnitEquilateralTriple
#print axioms check_unit_square_witness
#print axioms msl_fmz_erdos99_campaign_001_R004_L1
