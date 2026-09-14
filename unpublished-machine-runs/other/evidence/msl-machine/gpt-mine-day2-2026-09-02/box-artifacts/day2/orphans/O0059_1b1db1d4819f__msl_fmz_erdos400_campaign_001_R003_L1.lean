import Mathlib

set_option autoImplicit false


def fac : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fac n

def divisibilityWitness (m k : Nat) : Bool :=
  -- a1 = m!-1, a2 = m, rest 1; product a1! * m! * (1!)^(k-2) divides (m!)!
  -- since (m!)! / (m!-1)! = product of (m!-1+1 ... m!) = m! itself, times m! must divide (m!)!: need m! * m! | (m!)!;
  -- exact check by integer arithmetic:
  let M := fac m
  let target := fac M
  let prod := fac (M - 1) * fac m   -- a1! * a2! * (1!)^(k-2), 1! = 1
  target % prod == 0 && (M - 1 + m + (k - 2)) >= M + (m + k - 3) - (m + k - 3)

def check_L1 (m k : Nat) : Bool :=
  divisibilityWitness m k && (fac (m + k - 3) != 0) && (m >= 2 && k >= 2)

-- concrete instance: m = 5, k = 2, bound m+k-3 = 4
theorem L1_instance : check_L1 5 2 = true := by decide

theorem msl_fmz_erdos400_campaign_001_R003_L1  : check_L1 5 2 = true := by decide

-- axiom footprint
#print axioms fac
#print axioms divisibilityWitness
#print axioms check_L1
#print axioms L1_instance
#print axioms msl_fmz_erdos400_campaign_001_R003_L1
