import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

theorem msl_erdos1104_lem_r006_l1_c2 (chk : Nat → Int → Int → Bool) : ∃ (V : Nat → Rat → Bool), ∀ (n : Nat) (q : Rat), V n q = chk n q.num q.den := by sorry
