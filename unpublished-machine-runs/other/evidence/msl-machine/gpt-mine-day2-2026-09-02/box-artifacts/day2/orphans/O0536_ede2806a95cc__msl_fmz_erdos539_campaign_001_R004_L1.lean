import Mathlib

set_option autoImplicit false


def qVal (a b : Nat) : Nat := a / (Nat.gcd a b)

-- quotient-value set of A as a deduplicated list
def qSet (A : List Nat) : List Nat :=
  (A.flatMap (fun a => A.map (fun b => qVal a b))).eraseDups

-- Concrete check: A = {2, 3}, n = 2. Quotient values:
--   (2,2):1  (2,3):2  (3,2):3  (3,3):1  -> {1,2,3}, size 3 > 2.
def A2 : List Nat := [2, 3]

def check_h2 : Bool :=
  (qSet A2).length > A2.length

theorem msl_fmz_erdos539_campaign_001_R004_L1  : check_h2 = true := by decide

-- axiom footprint
#print axioms qVal
#print axioms qSet
#print axioms A2
#print axioms check_h2
#print axioms msl_fmz_erdos539_campaign_001_R004_L1
