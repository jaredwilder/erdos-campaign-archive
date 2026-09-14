import Mathlib

set_option autoImplicit false


def triples : List (Nat × Nat × Nat) :=
  (List.range 6).flatMap fun i =>
    (List.range 6).flatMap fun j =>
      (List.range 6).map fun k => (i+1, j+1, k+1)

def distinctTriples : List (Nat × Nat × Nat) :=
  triples.filter fun t => match t with | (a, b, c) => a < b ∧ b < c

def sums : List Nat :=
  distinctTriples.map fun t => match t with | (a, b, c) => a + b + c

def check_counting_core : Bool :=
  sums.all (fun s => s ≥ 6) ∧ sums.contains 6

theorem msl_fmz_erdos274_campaign_001_R001_L1  : check_counting_core = true := by decide

-- axiom footprint
#print axioms triples
#print axioms distinctTriples
#print axioms sums
#print axioms check_counting_core
#print axioms msl_fmz_erdos274_campaign_001_R001_L1
