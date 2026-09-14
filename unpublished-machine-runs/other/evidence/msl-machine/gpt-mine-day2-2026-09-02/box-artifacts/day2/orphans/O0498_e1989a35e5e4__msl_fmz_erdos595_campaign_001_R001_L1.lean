import Mathlib

set_option autoImplicit false


Lean 4, no Mathlib. (Repaired: coversC5 previously returned a function type, not Bool.)

-- Canonical 5-cycle on vertices 0..4 (K4-free: it has no triangles at all)
def c5 (a b : Nat) : Bool :=
  (a + 1) % 5 == b || (b + 1) % 5 == a

-- Color class k contains exactly one edge: {k, (k+1) mod 5}
def classAdj (k : Nat) (a b : Nat) : Bool :=
  a == k && b == (k + 1) % 5

-- Decidable: every edge of C5 is covered by some class (the enumeration core:
-- each edge gets its own class).
def checkCoverage : Bool :=
  (classAdj 0 0 1 || classAdj 1 0 1 || classAdj 2 0 1 || classAdj 3 0 1 || classAdj 4 0 1) &&
  (classAdj 0 1 2 || classAdj 1 1 2 || classAdj 2 1 2 || classAdj 3 1 2 || classAdj 4 1 2) &&
  (classAdj 0 2 3 || classAdj 1 2 3 || classAdj 2 2 3 || classAdj 3 2 3 || classAdj 4 2 3) &&
  (classAdj 0 3 4 || classAdj 1 3 4 || classAdj 2 3 4 || classAdj 3 3 4 || classAdj 4 3 4) &&
  (classAdj 0 4 0 || classAdj 1 4 0 || classAdj 2 4 0 || classAdj 3 4 0 || classAdj 4 4 0)

-- Decidable: each class holds at most one edge of C5 (count <= 1), hence no
-- class can contain the three edges of a triangle.
def cnt (k : Nat) : Nat :=
  (bif classAdj k 0 1 then 1 else 0) + (bif classAdj k 1 2 then 1 else 0) +
  (bif classAdj k 2 3 then 1 else 0) + (bif classAdj k 3 4 then 1 else 0) +
  (bif classAdj k 4 0 then 1 else 0)

def checkSingleton : Bool :=
  cnt 0 <= 1 && cnt 1 <= 1 && cnt 2 <= 1 && cnt 3 <= 1 && cnt 4 <= 1

-- Decidable: C5 is K4-free via the relevant sufficient check — it is triangle-free
-- on all 10 triples of distinct vertices of {0..4}.
def tri (adj : Nat -> Nat -> Bool) (a b c : Nat) : Bool :=
  adj a b && adj b c && adj a c

def checkTriangleFree : Bool :=
  !(tri c5 0 1 2) && !(tri c5 0 1 3) && !(tri c5 0 1 4) &&
  !(tri c5 0 2 3) && !(tri c5 0 2 4) && !(tri c5 0 3 4) &&
  !(tri c5 1 2 3) && !(tri c5 1 2 4) && !(tri c5 1 3 4) &&
  !(tri c5 2 3 4)

def checkAll : Bool :=
  checkTriangleFree && checkCoverage && checkSingleton

theorem msl_fmz_erdos595_campaign_001_R001_L1  : checkAll = true := by decide

-- axiom footprint
#print axioms c5
#print axioms classAdj
#print axioms checkCoverage
#print axioms cnt
#print axioms checkSingleton
#print axioms tri
#print axioms checkTriangleFree
#print axioms checkAll
#print axioms msl_fmz_erdos595_campaign_001_R001_L1
