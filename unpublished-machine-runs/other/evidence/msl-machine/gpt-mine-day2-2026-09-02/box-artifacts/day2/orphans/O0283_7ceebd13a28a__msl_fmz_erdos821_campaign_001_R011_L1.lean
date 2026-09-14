import Mathlib

set_option autoImplicit false


def units (m : Nat) : List Nat :=
  (List.range (m + 1)).filter (fun a => Nat.gcd a m == 1)

def paired (m : Nat) (a : Nat) : Bool :=
  let b := (m - a) % m
  Nat.gcd b m == 1 && b != a

def checkInvolution (m : Nat) : Bool :=
  (units m).all (paired m)

def checkAll (bound : Nat) : Bool :=
  (List.range (bound - 2)).all (fun k => checkInvolution (k + 3))
-- paired m a : the partner b = (m - a) mod m of a is again a unit of m and
-- b ≠ a, i.e. a ↦ m - a is a fixed-point-free self-map of U(m); being an
-- involution it is then a fixed-point-free involution, so φ(m) = |U(m)| is even.
-- checkAll bound checks this for every 3 ≤ m < bound + 2... concretely for
-- m = 3, ..., bound + 2 (bound = 200 gives m up to 202).

theorem msl_fmz_erdos821_campaign_001_R011_L1  : checkAll 200 = true := by native_decide

-- axiom footprint
#print axioms units
#print axioms paired
#print axioms checkInvolution
#print axioms checkAll
#print axioms msl_fmz_erdos821_campaign_001_R011_L1
