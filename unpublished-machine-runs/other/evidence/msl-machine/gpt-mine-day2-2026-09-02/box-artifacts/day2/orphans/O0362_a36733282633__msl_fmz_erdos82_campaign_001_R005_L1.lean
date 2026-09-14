import Mathlib

set_option autoImplicit false


def log2n (n : Nat) : Nat := Nat.log2 n
def Fw (k : Nat) : Nat := k  -- witness growth F(2^k) = c*log2(2^k) with c = 1: exactly the fixed lower bound, attained
def ratioBounded (K : Nat) : Bool :=
  (List.range (K+1)).all (fun k => k = 0 || (Fw k * 100 <= 1 * k * 100 + 0))
-- Fw(k)/log2(2^k) = k/k = 1 for every k ≥ 1: the ratio NEVER exceeds the fixed constant c = 1,
-- even though F(n) >= c*log2 n holds with equality at every checked point.
def check_insufficiency (K : Nat) : Bool := ratioBounded K && (List.range (K+1)).all (fun k => Fw k >= k)

theorem msl_fmz_erdos82_campaign_001_R005_L1  : check_insufficiency 200 = true := by decide

-- axiom footprint
#print axioms log2n
#print axioms Fw
#print axioms ratioBounded
#print axioms check_insufficiency
#print axioms msl_fmz_erdos82_campaign_001_R005_L1
