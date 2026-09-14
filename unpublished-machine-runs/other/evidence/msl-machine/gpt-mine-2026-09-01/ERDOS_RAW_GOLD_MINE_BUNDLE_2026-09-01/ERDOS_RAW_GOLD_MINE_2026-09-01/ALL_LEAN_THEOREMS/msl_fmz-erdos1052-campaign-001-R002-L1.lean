import Mathlib

set_option autoImplicit false

def unitaryDivisors (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d))
def properUnitaryDivisors (n : ℕ) : Finset ℕ := (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d))
def isUnitaryPerfect (n : ℕ) : Prop := (properUnitaryDivisors n).sum id = n ∧ 0 < n

theorem msl_fmz_erdos1052_campaign_001_R002_L1  : unitaryDivisors 6 = ({1, 2, 3, 6} : Finset ℕ) ∧ properUnitaryDivisors 6 = ({1, 2, 3} : Finset ℕ) ∧ (properUnitaryDivisors 6).sum id = 6 ∧ isUnitaryPerfect 6 := by
  decide
