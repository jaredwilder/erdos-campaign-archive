import Mathlib

set_option autoImplicit false


def phi (n : Nat) : Nat :=
  (List.range n).filter (fun k => Nat.gcd (k+1) n == 1) |>.length

def phiEven (m : Nat) : Bool := Nat.beven (phi m)

def check_range (lo hi : Nat) : Bool :=
  (List.range (hi - lo + 1)).all (fun i => phiEven (lo + i))

theorem msl_fmz_erdos821_campaign_001_R007_L1  : check_range 3 24 = true := by decide

-- axiom footprint
#print axioms phi
#print axioms phiEven
#print axioms check_range
#print axioms msl_fmz_erdos821_campaign_001_R007_L1
