import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def Refutes (A : Prop) : Prop := A → False

def IndependenceAboutAlpha (A : Prop) : Prop :=
  Refutes A ∧ ¬ Refutes A

def EvidenceForReplacement (A : Prop) : Prop :=
  ¬ A → Refutes A

theorem msl_erdos507_b_m01_c1_triv (A : Prop) : ∀ (hA : ¬ A), Refutes A := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
