import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

noncomputable def unitPairs {d : Nat} (s : Finset (EuclideanSpace ℝ (Fin d))) : Nat :=
  ((s ×ˢ s).filter (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      p.1 ≠ p.2 ∧ dist p.1 p.2 = (1 : ℝ))).card / 2

noncomputable def fd (d : Nat) (n : Nat) : Nat :=
  sSup {m : Nat | ∃ s : Finset (EuclideanSpace ℝ (Fin d)), s.card = n ∧ unitPairs s = m}

theorem msl_erdos1085_a_m02_composition (d : Nat) (g : Nat → ℝ) : ((∃ (c : ℝ), 0 < c ∧ ∀ (n : Nat), 1 ≤ n → c * g n ≤ (↑(fd d n) : ℝ)) ∧ (∃ (C : ℝ), 0 < C ∧ ∀ (n : Nat), 1 ≤ n → (↑(fd d n) : ℝ) ≤ C * g n)) → (∃ (c : ℝ) (C : ℝ), 0 < c ∧ 0 < C ∧ ∀ (n : Nat), 1 ≤ n → c * g n ≤ (↑(fd d n) : ℝ) ∧ (↑(fd d n) : ℝ) ≤ C * g n) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos1085_a_m02_composition
