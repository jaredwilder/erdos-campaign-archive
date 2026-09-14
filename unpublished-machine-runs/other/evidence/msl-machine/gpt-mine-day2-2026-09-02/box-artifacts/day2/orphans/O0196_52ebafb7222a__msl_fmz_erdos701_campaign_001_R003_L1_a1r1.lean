import Mathlib

set_option autoImplicit false


def powerset : List Nat → List (List Nat)
  | [] => [[]]
  | a :: as => let ps := powerset as; ps ++ ps.map (fun l => a :: l)

def maxL : List Nat → Nat := fun l => l.foldr max 0

-- Mathlib.Set.Intersecting convention, frozen: ALL pairs including A=B,
-- so every member of an intersecting family is nonempty (∅ &&& ∅ = 0).
def intersecting (fam : List Nat) : Bool :=
  fam.all fun a => fam.all fun b => a &&& b != 0

-- Families on X = {0,1,2}: a family is a sub-list of the 8 subset-bitmasks.
def allFams : List (List Nat) := powerset (List.range 8)

def hereditary (fam : List Nat) : Bool :=
  fam.all fun a => (List.range 8).all fun m =>
    m &&& a == m → fam.contains m

-- Max size of a pairwise-intersecting subfamily, and the largest star.
def maxInter (fam : List Nat) : Nat :=
  maxL ((powerset fam).filter intersecting |>.map List.length)

def maxStar (fam : List Nat) : Nat :=
  maxL ((List.range 3).map fun x =>
    fam.countP fun a => a &&& (1 <<< x) != 0)

-- Chvátal star bound holds for EVERY hereditary family on the 3-element ground set.
def check_n3 : Bool :=
  allFams.all fun fam =>
    hereditary fam = true → maxInter fam ≤ maxStar fam

theorem msl_fmz_erdos701_campaign_001_R003_L1_a1r1  : check_n3 = true := by decide

-- axiom footprint
#print axioms powerset
#print axioms maxL
#print axioms intersecting
#print axioms allFams
#print axioms hereditary
#print axioms maxInter
#print axioms maxStar
#print axioms check_n3
#print axioms msl_fmz_erdos701_campaign_001_R003_L1_a1r1
