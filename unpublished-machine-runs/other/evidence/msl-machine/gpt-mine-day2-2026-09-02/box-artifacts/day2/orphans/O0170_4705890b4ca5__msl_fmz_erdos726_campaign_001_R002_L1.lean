import Mathlib

set_option autoImplicit false


/-- Exact-halving check: for every n in [1, N], n*(n+1) is even, so the halved value n*(n+1)/2 is an exact integer (no rounding), and it satisfies the defining identity 2 * (n*(n+1)/2) = n*(n+1). This is the integer content of the parity-of-n(n+1) halving step that L1's induction relies on. -/
def halfOk : Nat → Bool
  | 0 => true
  | (n+1) =>
      let prod := (n+1) * ((n+1)+1)
      let h := prod / 2
      (2 * h == prod) && halfOk n

def check_halving (N : Nat) : Bool := halfOk N

theorem msl_fmz_erdos726_campaign_001_R002_L1  : check_halving 200 = true := by decide

-- axiom footprint
#print axioms halfOk
#print axioms check_halving
#print axioms msl_fmz_erdos726_campaign_001_R002_L1
