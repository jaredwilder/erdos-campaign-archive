import Mathlib

set_option autoImplicit false


def bigOmegaF : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel+1, m, d =>
      if m ≤ 1 then 0
      else if m % d == 0 then 1 + bigOmegaF fuel (m / d) d
      else bigOmegaF fuel m (d + 1)

def bigOmega (m : Nat) : Nat := bigOmegaF (2 * m + 2) m 2

def windowOK (k P n : Nat) : Bool :=
  let m := ((n + P - 1) / P) * P
  let q := m / P
  decide (n ≤ m) && decide (m < n + P) && decide (q ≥ 2) && decide (bigOmega m > k)

def nums (lo cnt : Nat) : List Nat := (List.range cnt).map (· + lo)

def the_check : Bool :=
  (nums 12 50).all (windowOK 2 6) &&
  (nums 60 50).all (windowOK 3 30) &&
  (nums 420 50).all (windowOK 4 210)

theorem msl_fmz_erdos891_campaign_001_R007_L1_a1r2  : the_check = true := by decide

-- axiom footprint
#print axioms bigOmegaF
#print axioms bigOmega
#print axioms windowOK
#print axioms nums
#print axioms the_check
#print axioms msl_fmz_erdos891_campaign_001_R007_L1_a1r2
