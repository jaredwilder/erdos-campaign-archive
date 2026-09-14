import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

theorem msl_erdos1104_lem_r006_l1_composition (ValidW : Nat → Rat → Prop) : ((∃ (chk : Nat → Int → Int → Bool), (∀ (n : Nat) (q : Rat), chk n q.num q.den = true ↔ ValidW n q) ∧ (∀ (n : Nat) (a : Int), chk n a 0 = false)) ∧ (∀ (chk : Nat → Int → Int → Bool), ∃ (V : Nat → Rat → Bool), ∀ (n : Nat) (q : Rat), V n q = chk n q.num q.den)) → (∃ (V : Nat → Rat → Bool) (chk : Nat → Int → Int → Bool), (∀ (n : Nat) (q : Rat), V n q = chk n q.num q.den) ∧ (∀ (n : Nat) (q : Rat), V n q = true ↔ ValidW n q) ∧ (∀ (n : Nat) (a : Int), chk n a 0 = false)) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos1104_lem_r006_l1_composition
