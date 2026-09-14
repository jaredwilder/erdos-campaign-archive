import Mathlib

set_option autoImplicit false

def exactSign (x : Int) : Int :=
  if x < 0 then -1 else if x > 0 then 1 else 0

def exactResolve (xs : List Int) : Option (List Int) :=
  if xs.any (fun x => x == 0) then none else some (xs.map exactSign)

theorem msl_fmz_erdos1_campaign_001_R002_L1  : ∀ xs : List Int,
    (exactResolve xs = none ↔ xs.any (fun x => x == 0) = true) ∧
    (exactResolve xs = some (xs.map exactSign) ↔ xs.any (fun x => x == 0) = false) := by
  intro xs
  simp only [exactResolve]
  by_cases h : xs.any (fun x => x == 0)
  · simp [h]
  · simp [h]
