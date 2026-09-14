import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

theorem msl_erdos1104_lem_r006_l1_c1 (ValidW : Nat → Rat → Prop) : ∃ (chk : Nat → Int → Int → Bool), (∀ (n : Nat) (q : Rat), chk n q.num q.den = true ↔ ValidW n q) ∧ (∀ (n : Nat) (a : Int), chk n a 0 = false) := by sorry
