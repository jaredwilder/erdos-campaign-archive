import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def Refutes (A : Prop) : Prop := A → False

def IndependenceAboutAlpha (A : Prop) : Prop :=
  Refutes A ∧ ¬ Refutes A

def EvidenceForReplacement (A : Prop) : Prop :=
  ¬ A → Refutes A

theorem msl_erdos507_b_m01_composition (A : Prop) : ((∀ (hA : ¬ A), Refutes A) ∧ (∀ (hA : ¬ A), EvidenceForReplacement A) ∧ (∀ (hA : ¬ A), ¬ IndependenceAboutAlpha A)) → (¬ A → Refutes A ∧ EvidenceForReplacement A ∧ ¬ IndependenceAboutAlpha A) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos507_b_m01_composition
