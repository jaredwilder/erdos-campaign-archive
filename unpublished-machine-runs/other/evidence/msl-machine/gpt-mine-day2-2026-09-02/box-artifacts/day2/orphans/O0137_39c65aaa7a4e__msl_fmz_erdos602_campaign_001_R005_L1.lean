import Mathlib

set_option autoImplicit false


def F : List (List Nat) :=
  [[12,112,13,113,14,114,1,11],
   [12,112,23,123,24,124,2,22],
   [13,113,23,123,34,134,3,33],
   [14,114,24,124,34,134,4,44]]
-- private (red) points x1..x4 and extra (blue) points y1..y4
def reds : List Nat := [1,2,3,4]
def col (p : Nat) : Nat := if p ∈ reds then 1 else 0
def interSize (A B : List Nat) : Nat := (A.filter (· ∈ B)).length
def pairwiseNe1 : Bool :=
  F.all (fun A => F.all (fun B => A = B ∨ interSize A B ≠ 1))
def hasRed (A : List Nat) : Bool := A.any (fun p => col p = 1)
def hasBlue (A : List Nat) : Bool := A.any (fun p => col p = 0)
def coloringGood : Bool := F.all (fun A => hasRed A && hasBlue A)
-- the greedy finite-core lemma, instantiated: for this explicit family the
-- private-point construction yields a 2-colouring with no monochromatic member

theorem msl_fmz_erdos602_campaign_001_R005_L1  : pairwiseNe1 = true ∧ coloringGood = true ∧ (∀ A ∈ F, A.length > 0) := by decide

-- axiom footprint
#print axioms F
#print axioms reds
#print axioms col
#print axioms interSize
#print axioms pairwiseNe1
#print axioms hasRed
#print axioms hasBlue
#print axioms coloringGood
#print axioms msl_fmz_erdos602_campaign_001_R005_L1
