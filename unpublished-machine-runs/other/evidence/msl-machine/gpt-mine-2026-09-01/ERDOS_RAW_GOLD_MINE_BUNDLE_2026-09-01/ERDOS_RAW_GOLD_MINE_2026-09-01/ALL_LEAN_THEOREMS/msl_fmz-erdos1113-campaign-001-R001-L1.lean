import Mathlib

set_option autoImplicit false

def verifier₁ (_input : List Nat) : Bool := false

def verifier₂ (_input : List Nat) : Bool := false

def issuesNonemptyCertificate (verifier : List Nat → Bool) : Prop :=
  ∃ input : List Nat, input ≠ ([] : List Nat) ∧ verifier input = true

theorem msl_fmz_erdos1113_campaign_001_R001_L1  : verifier₁ ([] : List Nat) = false ∧ verifier₂ ([] : List Nat) = false ∧ ¬ issuesNonemptyCertificate verifier₁ ∧ ¬ issuesNonemptyCertificate verifier₂ := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro h
    rcases h with ⟨input, hne, hok⟩
    simp [verifier₁] at hok
  · intro h
    rcases h with ⟨input, hne, hok⟩
    simp [verifier₂] at hok
