import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def BoundedCoverage (c : Nat → Bool) (B : Nat) : Prop := ∀ (n : Nat), n ≤ B → c n = true

def CertifiesAll (c : Nat → Bool) (P : Nat → Prop) : Prop := ∀ (n : Nat), c n = true ∧ P n

theorem msl_erdos1101_lem_r003_l1_c2 : ∀ (c : Nat → Bool), (∃ (n : Nat), c n = false) → ¬ CertifiesAll c (fun (_ : Nat) => True) := by sorry
