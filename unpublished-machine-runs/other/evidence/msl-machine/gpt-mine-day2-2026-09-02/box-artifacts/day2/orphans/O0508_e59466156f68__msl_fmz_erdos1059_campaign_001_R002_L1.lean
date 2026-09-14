import Mathlib

set_option autoImplicit false


-- Bounded (decidable) compositeness test: n composite iff it has a proper divisor in [2, n-1].
def isComposite (n : Nat) : Bool :=
  2 ≤ n ∧ (List.range (n - 2)).any (fun d => n % (d + 2) = 0)

-- L1's k=1 conjunct: p - 1! = p - 1 must be composite.
def conjunct_k1 (p : Nat) : Bool := isComposite (p - 1)

-- Boundary instances named in the standing lemma record: p = 3 and p = 5.
def check_L1_boundary : Bool :=
  (conjunct_k1 5 == true) ∧ (conjunct_k1 3 == false)

theorem msl_fmz_erdos1059_campaign_001_R002_L1  : check_L1_boundary = true := by decide

-- axiom footprint
#print axioms isComposite
#print axioms conjunct_k1
#print axioms check_L1_boundary
#print axioms msl_fmz_erdos1059_campaign_001_R002_L1
