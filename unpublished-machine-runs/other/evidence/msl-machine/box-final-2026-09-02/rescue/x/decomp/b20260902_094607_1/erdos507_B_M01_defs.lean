import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def Refutes (A : Prop) : Prop := A → False

def IndependenceAboutAlpha (A : Prop) : Prop :=
  Refutes A ∧ ¬ Refutes A

def EvidenceForReplacement (A : Prop) : Prop :=
  ¬ A → Refutes A
