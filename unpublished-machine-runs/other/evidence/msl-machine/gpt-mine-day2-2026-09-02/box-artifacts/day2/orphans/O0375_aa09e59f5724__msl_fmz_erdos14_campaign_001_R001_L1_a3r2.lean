import Mathlib

set_option autoImplicit false


def witnessA : List Nat := [1, 2, 4, 8, 16, 32]
def sumPairs (A : List Nat) : List (Nat × Nat) :=
  A.flatMap (fun a => (A.filter (fun b => a ≤ b)).map (fun b => (a, b)))
def rA (A : List Nat) (n : Nat) : Nat :=
  (sumPairs A).filter (fun p => p.1 + p.2 == n) |>.length
def nonUniqueCount (A : List Nat) (N : Nat) : Nat :=
  (List.range N).filter (fun m => rA A (m + 1) != 1) |>.length
def check_witness : Bool := nonUniqueCount witnessA 64 == 43
theorem L1_instance : check_witness = true := by decide

theorem msl_fmz_erdos14_campaign_001_R001_L1_a3r2  : check_witness = true := by decide

-- axiom footprint
#print axioms witnessA
#print axioms sumPairs
#print axioms rA
#print axioms nonUniqueCount
#print axioms check_witness
#print axioms L1_instance
#print axioms msl_fmz_erdos14_campaign_001_R001_L1_a3r2
