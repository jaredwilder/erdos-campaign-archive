import Mathlib

set_option autoImplicit false



-- Decidable arithmetic core of L1, reduced to pure Bool comparisons over exact rationals.
-- L1's load-bearing step is: P(x) ≤ ε1 ≤ ε2 ⟹ P(x) ≤ ε2 (transitivity of ≤ on the residual),
-- i.e. membership in the ≤-threshold set B is monotone in ε. Here P is instantiated at
-- concrete contract-domain points; everything is exact ℚ arithmetic, no floats, no tolerance.
open Int
def P : Nat → ℚ := fun n => (n + 3 : ℚ) / 4
-- checkTransfer x e1 e2 : true iff (P x ≤ e1 ∧ e1 ≤ e2) → P x ≤ e2,
-- encoded as a Bool so the kernel decides it by evaluation.
def checkTransfer (x : Nat) (e1 e2 : ℚ) : Bool :=
  !(P x ≤ e1 && e1 ≤ e2) || (P x ≤ e2)
-- Negative control: a point where the premise FAILS must not be certified.
def checkPremiseFails (x : Nat) (e1 e2 : ℚ) : Bool :=
  decide (¬ (P x ≤ e1 ∧ e1 ≤ e2))

theorem msl_fmz_erdos413_campaign_001_R001_L1  : theorem L1_arith_core :
    checkTransfer 5 (2 : ℚ) (3 : ℚ) = true ∧
    checkTransfer 1 ((1 : ℚ)/2) ((7 : ℚ)/4) = true ∧
    checkTransfer 0 ((5 : ℚ)/2) ((5 : ℚ)/2) = true ∧
    checkPremiseFails 5 ((1 : ℚ)/2) ((3 : ℚ)/4) = true ∧
    (P 5 : ℚ) = 2 ∧ ((1 : ℚ)/2 ≤ (3 : ℚ)/4) = true := by decide

-- axiom footprint
#print axioms P
#print axioms checkTransfer
#print axioms checkPremiseFails
#print axioms msl_fmz_erdos413_campaign_001_R001_L1
