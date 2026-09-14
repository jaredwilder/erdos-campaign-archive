import Mathlib

set_option autoImplicit false


def divides (d p : Nat) : Bool := p % d == 0

/-- Trial-division kernel, non-recursively: a candidate divisor is any d with 2 <= d, d*d <= p, i.e. d <= p/2, drawn from a precomputed range; divisibility is one exact `mod` check. -/
def trialPrime (p : Nat) : Bool :=
  if p < 2 then false
  else not (List.any (List.range (p / 2 + 1)) (fun d =>
    let d := d + 2
    d * d <= p && divides d p))

def expected : List (Nat × Bool) :=
  [(0, false), (1, false), (2, true), (3, true), (4, false), (5, true),
   (7, true), (8, false), (9, false), (11, true), (23, true), (24, false),
   (25, false), (29, true), (97, true), (91, false), (89, true)]

def checkAll : List (Nat × Bool) -> Bool
  | [] => true
  | (p, b) :: rest => (trialPrime p == b) && checkAll rest

def check_witness : Bool := checkAll expected

theorem msl_fmz_erdos1055_campaign_001_R002_L1  : check_witness = true := by decide

-- axiom footprint
#print axioms divides
#print axioms trialPrime
#print axioms expected
#print axioms checkAll
#print axioms check_witness
#print axioms msl_fmz_erdos1055_campaign_001_R002_L1
