import Mathlib

set_option autoImplicit false


def pairsum_count (k : Nat) : Nat := k * (k + 1) / 2

def value_set_size (N : Nat) : Nat := 2 * N - 1

def counting_bound_holds (N k : Nat) : Bool :=
  pairsum_count k ≤ value_set_size N

def sidon_upper_exceeds (N k : Nat) : Bool :=
  pairsum_count k > value_set_size N

theorem msl_fmz_erdos340_campaign_001_R002_L1  : counting_bound_holds 100 19 = true ∧ sidon_upper_exceeds 100 20 = true := by decide

-- axiom footprint
#print axioms pairsum_count
#print axioms value_set_size
#print axioms counting_bound_holds
#print axioms sidon_upper_exceeds
#print axioms msl_fmz_erdos340_campaign_001_R002_L1
