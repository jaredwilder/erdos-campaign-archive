import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def erdos306R003L : Finset ℕ := {6, 10, 14, 15, 21, 22}

theorem msl_erdos306_lem_r003_l1_c2 : ∀ d ∈ erdos306R003L, ω d = 2 ∧ Ω d = 2 := by sorry
