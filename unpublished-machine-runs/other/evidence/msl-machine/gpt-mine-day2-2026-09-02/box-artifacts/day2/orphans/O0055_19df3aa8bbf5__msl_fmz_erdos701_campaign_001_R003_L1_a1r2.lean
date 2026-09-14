import Mathlib

set_option autoImplicit false


def powerset : List Nat → List (List Nat)
  | [] => [[]]
  | a :: as => let ps := powerset as; ps ++ ps.map (fun l => a :: l)

def maxL : List Nat → Nat := fun l => l.foldr max 0

-- Frozen all-pairs Set.Intersecting convention: every pair (a,b) incl. a=b,
-- so an intersecting subfamily contains no empty set (bitmask 0).
def intersecting (fam : List Nat) : Bool :=
  fam.all fun a => fam.all fun b => a &&& b != 0

def hereditary (fam : List Nat) : Bool :=
  fam.all fun a => (List.range 4).all fun m =>
    m &&& a == m → fam.contains m

-- Families on X = {0,1}: sub-lists of the 4 subset-bitmasks 0,1,2,3.
def allFams : List (List Nat) := powerset (List.range 4)

def maxInter (fam : List Nat) : Nat :=
  maxL ((powerset fam).filter intersecting |>.map List.length)

def maxStar (fam : List Nat) : Nat :=
  maxL ((List.range 2).map fun x =>
    fam.countP fun a => a &&& (1 <<< x) != 0)

-- Chvátal star bound for EVERY hereditary family on the 2-element ground set.
def check_n2 : Bool :=
  allFams.all fun fam =>
    hereditary fam = true → maxInter fam ≤ maxStar fam

theorem msl_fmz_erdos701_campaign_001_R003_L1_a1r2  : check_n2 = true := by decide

-- axiom footprint
#print axioms powerset
#print axioms maxL
#print axioms intersecting
#print axioms hereditary
#print axioms allFams
#print axioms maxInter
#print axioms maxStar
#print axioms check_n2
#print axioms msl_fmz_erdos701_campaign_001_R003_L1_a1r2
