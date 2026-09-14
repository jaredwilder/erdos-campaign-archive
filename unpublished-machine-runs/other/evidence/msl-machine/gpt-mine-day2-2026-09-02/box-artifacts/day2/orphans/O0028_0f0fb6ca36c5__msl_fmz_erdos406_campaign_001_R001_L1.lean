import Mathlib

set_option autoImplicit false



/-- All base-`b` digits of `m` are `< 2`. Total, computable, structurally recursive on m/b. -/
def digits01Base (b : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 =>
    let q := (m + 1) / b
    let r := (m + 1) % b
    r < 2 && digits01Base b q

/-- Every power of 2 has only digits {0,1} in base 2 (computable half of L1's transfer). -/
def checkTransfer (N : ℕ) : Bool :=
  (List.range (N+1)).all (fun n => digits01Base 2 (2 ^ n))

/-- Decidable census: n ≤ N with 2^n having only digits {0,1} in base 3. -/
def base3Census (N : ℕ) : List ℕ :=
  (List.range (N+1)).filter (fun n => digits01Base 3 (2 ^ n))

theorem msl_fmz_erdos406_campaign_001_R001_L1  : checkTransfer 20 = true ∧ base3Census 20 = [0, 1, 3] := by decide

-- axiom footprint
#print axioms digits01Base
#print axioms checkTransfer
#print axioms base3Census
#print axioms msl_fmz_erdos406_campaign_001_R001_L1
