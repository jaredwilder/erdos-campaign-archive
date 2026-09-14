import Mathlib

set_option autoImplicit false


/-- Euler phi by exhaustive coprimality count (exact, Nat). -/
def phiD (d : Nat) : Nat :=
  ((List.range d).filter (fun k => Nat.gcd k d = 1)).length

/-- Least n in [0,40) congruent to a mod d (ordered search = minimality). -/
def leastResidue (a d : Nat) : Nat :=
  ((List.range 40).filter (fun n => n % d == a)).head!

/-- Exact-rational, float-free verifier core: phi counting, ordered residue-class
    search, and rational inequality evaluation — Nat equality and Rat `<` only. -/
def checkVerifier : Bool :=
  phiD 10 == 4 ∧
  phiD 12 == 4 ∧
  phiD 7 == 6 ∧
  leastResidue 2 3 == 2 ∧
  leastResidue 3 7 == 3 ∧
  leastResidue 4 9 == 4 ∧
  ((13 : Rat) > (1 + 1/10) * (6 : Rat) * (11/10)) ∧
  ¬ ((5 : Rat) > (1 + 1/10) * (2 : Rat) * (11/10))

theorem msl_fmz_erdos971_campaign_001_R009_L1  : checkVerifier = true := by decide
