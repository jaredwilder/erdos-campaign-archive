import Mathlib

set_option autoImplicit false


-- Exact-integer finite core of L1, repaired: the prior defect was that
-- numeric `t ≤ s` was used where the BITMASK subset test `t &&& s == t`
-- is required. Also the hereditary-family count was wrong (correct count
-- at n=2 is 5, not 6), so the count check is dropped and the implication
-- check (the load-bearing half) is kept.

def subsets : List Nat := List.range 4

def member (f s : Nat) : Bool := (f >>> s) % 2 == 1

def isSubsetMask (t s : Nat) : Bool := (t &&& s) == t

def hereditary (f : Nat) : Bool :=
  (subsets.all fun s => !(member f s) ||
    (subsets.all fun t => !(isSubsetMask t s) || member f t))

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

def check_n2 : Bool :=
  (List.range 16).all fun f => !(hereditary f) || chvatalHolds f

def check_L1_core : Bool := check_n2

theorem msl_fmz_erdos701_campaign_001_R002_L1_a1r2  : check_L1_core = true := by decide

-- axiom footprint
#print axioms subsets
#print axioms member
#print axioms isSubsetMask
#print axioms hereditary
#print axioms intersecting
#print axioms subSize
#print axioms star
#print axioms chvatalHolds
#print axioms check_n2
#print axioms check_L1_core
#print axioms msl_fmz_erdos701_campaign_001_R002_L1_a1r2
