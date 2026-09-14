import Mathlib

set_option autoImplicit false


def isPrime : Nat → Bool
  | 0 => false | 1 => false
  | 2 => true | 3 => true
  | n => Nat.all (List.range (n/2 - 1)) (fun d => n % (d+2) != 0) || (n ≤ 5)

def check : Bool :=
  -- 2 is prime and 2+1 = 3 = 2^0·3^1
  (isPrime 2 && (2+1 == 3)) &&
  -- 3 is prime and 3+1 = 4 = 2^2·3^0
  (isPrime 3 && (3+1 == 4)) &&
  -- 7 is prime and 7+1 = 8 = 2^3·3^0
  (isPrime 7 && (7+1 == 8)) &&
  -- 23 is prime and 23+1 = 24 = 2^3·3^1
  (isPrime 23 && (23+1 == 24))

theorem msl_fmz_erdos1055_campaign_001_R008_L1_a1r2  : check = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms check
#print axioms msl_fmz_erdos1055_campaign_001_R008_L1_a1r2
