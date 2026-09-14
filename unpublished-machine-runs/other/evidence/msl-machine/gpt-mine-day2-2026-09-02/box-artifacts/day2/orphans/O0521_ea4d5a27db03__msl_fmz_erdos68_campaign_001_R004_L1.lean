import Mathlib

set_option autoImplicit false


def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

def pow' : Nat → Nat → Nat
  | _, 0 => 1
  | b, k+1 => b * pow' b k

-- Sum_{j=1}^{J} (n!)^{J-j}, i.e. the geometric sum without the j=0 term.
def geoSum (n J : Nat) : Nat :=
  (List.range J).foldl (fun acc j => acc + pow' (fact n) (J - 1 - j)) 0

-- Rational identity (n!-1) * Σ_{j=1}^{J} (n!)^{-j} = 1 - (n!)^{-J},
-- cleared of denominators by multiplying through by (n!)^J:
--   (n!-1) * Σ_{j=1}^{J} (n!)^{J-j} = (n!)^J - 1.
def checkIdentity (n J : Nat) : Bool :=
  (fact n - 1) * geoSum n J == pow' (fact n) J - 1

-- Fragment check: identity verified for all 2 ≤ n ≤ 60 and 1 ≤ J ≤ 40.
def checkAll (Nmax Jmax : Nat) : Bool :=
  (List.range (Nmax - 1)).all (fun i =>
    (List.range Jmax).all (fun j => checkIdentity (i + 2) (j + 1)))

theorem msl_fmz_erdos68_campaign_001_R004_L1  : checkAll 60 40 = true := by decide

-- axiom footprint
#print axioms fact
#print axioms pow'
#print axioms geoSum
#print axioms checkIdentity
#print axioms checkAll
#print axioms msl_fmz_erdos68_campaign_001_R004_L1
