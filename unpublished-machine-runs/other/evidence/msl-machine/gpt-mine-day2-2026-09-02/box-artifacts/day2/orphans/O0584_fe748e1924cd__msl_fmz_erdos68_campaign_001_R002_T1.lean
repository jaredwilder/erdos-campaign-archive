import Mathlib

set_option autoImplicit false


def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

def powN (N : Nat) : Nat → Nat
  | 0 => 1
  | k+1 => N * powN N k

-- exact rational partial sum Σ_{j=1}^k N^{-j} as (num, den), built by
-- cross-multiplication only (no floats, no gcd):
-- step: num/den + 1/N^j = (num*N^j + den) / (den*N^j)
def geoSum (N : Nat) : Nat → Nat × Nat
  | 0 => (0, 1)
  | k+1 =>
      let p := powN N (k+1)
      let (num, den) := geoSum N k
      (num * p + den, den * p)

-- Two exact checks for one (n, k), N := fact n ≥ 2:
-- (a) closed form:  Σ_{j=1}^k N^{-j} = (N^k − 1) / ((N−1)·N^k)
--     cross-multiplied: sNum * ((N−1)·N^k) = (N^k − 1) * sDen
-- (b) exact remainder identity:  1/(N−1) = Σ + N^{−k}/(N−1)
--     cross-multiplied against the geoSum representation:
--     (N−1)·sNum + sDen/N^k = sDen   (division exact since sDen = N^k·M)
def check (n k : Nat) : Bool :=
  let N := fact n
  let (sNum, sDen) := geoSum N k
  (sNum * ((N - 1) * powN N k) = (powN N k - 1) * sDen)
    && ((N - 1) * sNum + sDen / powN N k = sDen)

theorem T1_holds :
    check 2 3 = true ∧ check 2 4 = true ∧ check 3 2 = true ∧ check 3 3 = true :=
  by decide

theorem msl_fmz_erdos68_campaign_001_R002_T1  : check 2 3 = true ∧ check 2 4 = true ∧ check 3 2 = true ∧ check 3 3 = true := by decide

-- axiom footprint
#print axioms fact
#print axioms powN
#print axioms geoSum
#print axioms check
#print axioms T1_holds
#print axioms msl_fmz_erdos68_campaign_001_R002_T1
