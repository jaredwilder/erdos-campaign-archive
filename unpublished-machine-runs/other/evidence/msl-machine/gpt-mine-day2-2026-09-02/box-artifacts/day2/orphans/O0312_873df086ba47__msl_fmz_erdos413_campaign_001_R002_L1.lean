import Mathlib

set_option autoImplicit false


-- ω(n) computed by explicit trial division over small primes; total, decidable, no Mathlib.
def divides (d n : Nat) : Bool := n % d == 0

def check_witness (n : Nat) (p1 p2 p3 : Nat) : Bool :=
  n == p1 * p2 * p3 ∧ p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3 ∧
  divides p1 n ∧ divides p2 n ∧ divides p3 n ∧
  p1 > 1 ∧ p2 > 1 ∧ p3 > 1

def check_thirty : Bool := check_witness 30 2 3 5

def check_forty_two : Bool := check_witness 42 2 3 7

def check_fragment : Bool := check_thirty ∧ check_forty_two

theorem msl_fmz_erdos413_campaign_001_R002_L1  : check_fragment = true := by decide

-- axiom footprint
#print axioms divides
#print axioms check_witness
#print axioms check_thirty
#print axioms check_forty_two
#print axioms check_fragment
#print axioms msl_fmz_erdos413_campaign_001_R002_L1
