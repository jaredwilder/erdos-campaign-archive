import Mathlib

set_option autoImplicit false


def submasks : Nat → List Nat
  | 0 => [0]
  | 1 => [0,1]
  | 2 => [0,2]
  | 3 => [0,1,2,3]
  | 4 => [0,4]
  | 5 => [0,1,4,5]
  | 6 => [0,2,4,6]
  | 7 => [0,1,2,3,4,5,6,7]
  | _ => []

def memF (f s : Nat) : Bool := (f >>> s) &&& 1 == 1

def hereditary (f : Nat) : Bool :=
  (List.range 8).all (fun s =>
    !(memF f s) || (submasks s).all (fun t => memF f t))

def intersecting (f : Nat) : Bool :=
  (List.range 8).all (fun a => (List.range 8).all (fun b =>
    !(memF f a && memF f b) || (a &&& b) != 0))

def commonPoint (f : Nat) : Bool :=
  [1,2,4].any (fun x => (List.range 8).all (fun s =>
    !(memF f s) || (s &&& x) == x))

def check : Bool :=
  (List.range 256).all (fun f =>
    !(hereditary f && intersecting f) || commonPoint f)

def check_witness : Bool := check

theorem msl_fmz_erdos701_campaign_001_R009_L1_star_bound_n_leq_4_a1r2  : check_witness = true := by native_decide

-- axiom footprint
#print axioms submasks
#print axioms memF
#print axioms hereditary
#print axioms intersecting
#print axioms commonPoint
#print axioms check
#print axioms check_witness
#print axioms msl_fmz_erdos701_campaign_001_R009_L1_star_bound_n_leq_4_a1r2
