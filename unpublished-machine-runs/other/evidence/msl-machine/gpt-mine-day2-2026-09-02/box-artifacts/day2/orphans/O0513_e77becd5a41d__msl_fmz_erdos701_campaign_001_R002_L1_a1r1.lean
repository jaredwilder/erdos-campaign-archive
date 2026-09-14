import Mathlib

set_option autoImplicit false


-- Exact-integer finite core of L1: hereditary families on a 2-element
-- ground set, encoded as bitmasks over the 4 Venn atoms (subsets of {0,1});
-- all-pairs Set.Intersecting convention (self-pairs included, so a family
-- containing the empty set is never intersecting); exhaustive fail-closed check.

def subsets : List Nat := List.range 4

def member (f s : Nat) : Bool := (f >>> s) % 2 == 1

def hereditary (f : Nat) : Bool :=
  (subsets.all fun s => !(member f s) ||
    (subsets.all fun t => !(t ≤ s) || member f t))

def intersecting (g : Nat) : Bool :=
  (subsets.all fun a => !(member g a) ||
    (subsets.all fun b => !(member g b) || (a &&& b) != 0))

def subSize (g : Nat) : Nat := (subsets.filter (fun s => member g s)).length

def star (f x : Nat) : Nat :=
  (subsets.filter (fun s => member f s && (s &&& (1 <<< x)) != 0)).length

def chvatalHolds (f : Nat) : Bool :=
  (List.range 2).any fun x =>
    (List.range 16).all fun g =>
      !((g &&& f) == g) || !(intersecting g) || (subSize g ≤ star f x)

def countHereditary : Nat :=
  ((List.range 16).filter hereditary).length

def check_n2 : Bool :=
  (List.range 16).all fun f => !(hereditary f) || chvatalHolds f

def check_L1_core : Bool := check_n2 && (countHereditary == 6)

theorem msl_fmz_erdos701_campaign_001_R002_L1_a1r1  : check_L1_core = true := by decide

-- axiom footprint
#print axioms subsets
#print axioms member
#print axioms hereditary
#print axioms intersecting
#print axioms subSize
#print axioms star
#print axioms chvatalHolds
#print axioms countHereditary
#print axioms check_n2
#print axioms check_L1_core
#print axioms msl_fmz_erdos701_campaign_001_R002_L1_a1r1
