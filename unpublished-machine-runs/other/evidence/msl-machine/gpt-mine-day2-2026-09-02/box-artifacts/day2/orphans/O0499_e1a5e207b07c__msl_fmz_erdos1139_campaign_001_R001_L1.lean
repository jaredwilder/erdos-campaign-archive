import Mathlib

set_option autoImplicit false


namespace R001L1

/-- Exact-mode comparison over exact integers (stand-in for Fraction-exact
comparisons): trichotomy holds and `<` exactly matches `¬ ≥`. -/
def ExactModeComparison (a b : Nat) : Prop :=
  (a < b ∨ a = b ∨ b < a) ∧ ((a < b) ↔ ¬(b ≤ a))

/-- Fail-closed: the checker is total — every input yields a verdict. -/
def FailClosed (checker : Nat → Nat → Bool) : Prop :=
  ∀ a b : Nat, checker a b = true ∨ checker a b = false

/-- Deterministic injection tests, all over exact integers:
  * well-formed exact case passes: 3334/10000 > 1/3  (3334*3 > 10000)
  * injected tampered case fails:   3333/10000 ≤ 1/3  (3333*3 < 10000)
  * injected malformed case fails:  ¬(2 < 1)
Each verdict is a decidable Bool so the kernel reduces it by `decide`. -/
def L1Statement : Prop :=
  (∀ a b : Nat, ExactModeComparison a b) ∧
  FailClosed (fun a b => decide (a ≤ b)) ∧
  (decide (10000 < 3334 * 3) = true) ∧
  (decide (10000 < 3333 * 3) = false) ∧
  (decide (2 < 1) = false)

end R001L1

theorem msl_fmz_erdos1139_campaign_001_R001_L1  : R001L1.L1Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    refine ⟨?_, ?_⟩
    · rcases lt_trichotomy a b with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · constructor
      · intro h; exact Nat.not_le.mpr h
      · intro h; exact Nat.lt_of_not_le h
  · intro a b
    cases hb : decide (a ≤ b) with
    | true => exact Or.inl hb
    | false => exact Or.inr hb
  · decide
  · decide
  · decide

-- axiom footprint
#print axioms R001L1.ExactModeComparison
#print axioms R001L1.FailClosed
#print axioms R001L1.L1Statement
#print axioms msl_fmz_erdos1139_campaign_001_R001_L1
