import Mathlib

set_option autoImplicit false


def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _+1 => 0
  | n+1, k+1 => binom n (k+1) + binom n k

def lpfAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel+1, n, d =>
      if n ≤ 1 then 1
      else if d * d > n then n
      else if n % d == 0 then lpfAux fuel (n / d) d
      else lpfAux fuel n (d + 1)

def lpf (n : Nat) : Nat := lpfAux (n + 2) n 2

def checkR007L1 : Bool :=
  -- W1 = (n,k) = (9,2): C(9,2) = 36 = 2^2*3^2, largest prime factor 3
  (binom 9 2 == 36) && (2*2*3*3 == 36) && (lpf 36 == 3) &&
  -- W1 violates at c = 3/4: 3 < n-k+1 = 8  and  3 < 2^(7/4)  (3^4 = 81 < 2^7 = 128)
  ((3 < 9 - 2 + 1) && (3*3*3*3 < 2^7)) &&
  -- W1 violates at c = 1: 3 < 8  and  3 < 2^2 = 4
  ((3 < 9 - 2 + 1) && (3 < 2*2)) &&
  -- W2 = (n,k) = (10,3): C(10,3) = 120 = 2^3*3*5, largest prime factor 5
  (binom 10 3 == 120) && (2*2*2*3*5 == 120) && (lpf 120 == 5) &&
  -- W2 violates at c = 1/2: 5 < 8  and  5 < 3^(3/2)  (5^2 = 25 < 3^3 = 27)
  ((5 < 10 - 3 + 1) && (5*5 < 3*3*3)) &&
  -- W2 violates at c = 3/4: 5 < 8  and  5 < 3^(7/4)  (5^4 = 625 < 3^7 = 2187)
  ((5 < 10 - 3 + 1) && (5*5*5*5 < 3^7)) &&
  -- W2 violates at c = 1: 5 < 8  and  5 < 3^2 = 9
  ((5 < 10 - 3 + 1) && (5 < 3*3))

theorem msl_fmz_erdos683_campaign_001_R007_L1_a1r1  : checkR007L1 = true := by decide

-- axiom footprint
#print axioms binom
#print axioms lpfAux
#print axioms lpf
#print axioms checkR007L1
#print axioms msl_fmz_erdos683_campaign_001_R007_L1_a1r1
