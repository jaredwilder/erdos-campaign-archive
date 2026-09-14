import Mathlib

set_option autoImplicit false


def divisors (n : Nat) : List Nat := (List.range (n+1)).filter (fun d => n % d == 0)

def isSubsetSum (s : List Nat) (target : Nat) : Bool :=
  s.foldl (fun accs a => accs ++ accs.map (fun x => x + a)) [0] |>.contains target

def check_L001_fragment : Bool :=
  -- certificate 1: 15 = 1+2+4+8 with {1,2,4,8} subset of div(8); bound 8 < 33
  (isSubsetSum [1,2,4,8] 15) &&
  ([1,2,4,8].all (fun d => 8 % d == 0)) &&
  (1+2+4+8 == 15) && (8 < 33) &&
  -- certificate 2: 25 = 1+2+3+4+6+9 with each term a divisor of 36; bound 36 < 143
  (isSubsetSum [1,2,3,4,6,9] 25) &&
  ([1,2,3,4,6,9].all (fun d => 36 % d == 0)) &&
  (1+2+3+4+6+9 == 25) && (36 < 143)

theorem msl_fmz_erdos454_campaign_001_R001_L001  : check_L001_fragment = true := by decide

-- axiom footprint
#print axioms divisors
#print axioms isSubsetSum
#print axioms check_L001_fragment
#print axioms msl_fmz_erdos454_campaign_001_R001_L001
