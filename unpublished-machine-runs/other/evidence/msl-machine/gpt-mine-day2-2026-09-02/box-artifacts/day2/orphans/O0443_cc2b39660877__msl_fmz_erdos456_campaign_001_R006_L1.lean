import Mathlib

set_option autoImplicit false


def coprime (a b : Nat) : Bool := Nat.gcd a b == 1

def countCoprime (p : Nat) : Nat :=
  (List.range (p - 1)).filter (fun k => coprime (k + 1) p) |>.length

def phiEq (p : Nat) : Bool := countCoprime p == p - 1

def isPrimeCert (p : Nat) : Bool :=
  2 <= p && !(List.range (p - 1)).any (fun k => Nat.gcd (k + 1) p != 1)

def checkRange (n : Nat) : Bool :=
  (List.range (n - 1)).all (fun i =>
    let p := i + 2
    !isPrimeCert p || phiEq p)

theorem msl_fmz_erdos456_campaign_001_R006_L1  : checkRange 20 = true := by decide

-- axiom footprint
#print axioms coprime
#print axioms countCoprime
#print axioms phiEq
#print axioms isPrimeCert
#print axioms checkRange
#print axioms msl_fmz_erdos456_campaign_001_R006_L1
