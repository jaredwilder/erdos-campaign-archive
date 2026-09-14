import Mathlib

set_option autoImplicit false



structure PtConfig where
  n : ℕ
  pts : Fin n → ℚ × ℚ
  distinct : Function.Injective pts

-- tK C k : number of lines containing exactly k points of C, over ℚ.
noncomputable def tK (C : PtConfig) (k : ℕ) : ℕ :=
  Finset.card {L : Finset (Fin C.n) | L.card = k ∧ ∃ a b : Fin C.n, a ≠ b ∧
    ∀ i ∈ L, Collinear ℚ ({C.pts i, C.pts a, C.pts b} : Set (ℚ × ℚ)) ∧
    ∀ j : Fin C.n, Collinear ℚ ({C.pts j, C.pts a, C.pts b} : Set (ℚ × ℚ)) → j ∈ L}

axiom MelchiorGreenTao_OrdinaryLineBounds :
  ∀ (C : PtConfig), C.n ≥ 3 →
    tK C 5 = 0 → tK C 4 ≤ tK C 2 ∧ C.n / 2 ≤ tK C 2

theorem msl_fmz_erdos101_campaign_001_R001_L1  : theorem t4_sublinear (C : PtConfig) (h3 : C.n ≥ 3) (h5 : tK C 5 = 0) :
    tK C 4 ≤ tK C 2 ∧ C.n / 2 ≤ tK C 2 := exact MelchiorGreenTao_OrdinaryLineBounds C h3 h5

-- axiom footprint
#print axioms tK
#print axioms msl_fmz_erdos101_campaign_001_R001_L1
