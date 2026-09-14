import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def BoundedCoverage (c : Nat → Bool) (B : Nat) : Prop := ∀ (n : Nat), n ≤ B → c n = true

def CertifiesAll (c : Nat → Bool) (P : Nat → Prop) : Prop := ∀ (n : Nat), c n = true ∧ P n

theorem msl_erdos1101_lem_r003_l1_parent : ∃ (c : Nat → Bool) (P : Nat → Prop), BoundedCoverage c 8 ∧ ¬ CertifiesAll c P := by sorry
