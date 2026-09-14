import Mathlib

set_option autoImplicit false


def omega : Nat -> Nat  -- total, computable: count prime factors with multiplicity
  | 0 => 0
  | 1 => 0
  | n => 1 + omega (n / (smallestFactor n))
where smallestFactor n is the least d >= 2 dividing n (found by bounded search; total since d = n works).

def hasTripleFactorInWindow (n : Nat) : Bool :=
  (List.range 6).any (fun i => omega (n + i) >= 3)

def check_L1 (lo hi : Nat) : Bool :=
  (List.range (hi - lo + 1)).all (fun i => hasTripleFactorInWindow (lo + i))

theorem msl_fmz_erdos891_campaign_001_R004_L1_a1r1  : check_L1 9 10000 = true := by decide

-- axiom footprint
#print axioms omega
#print axioms hasTripleFactorInWindow
#print axioms check_L1
#print axioms msl_fmz_erdos891_campaign_001_R004_L1_a1r1
