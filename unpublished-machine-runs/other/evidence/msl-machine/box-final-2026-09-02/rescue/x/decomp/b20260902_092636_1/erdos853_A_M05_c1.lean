import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter Real

noncomputable def p853 (n : Nat) : Nat := Nat.nth (fun (m : Nat) => Nat.Prime m) n
noncomputable def d853 (n : Nat) : Nat := p853 (n + 2) - p853 (n + 1)
noncomputable def r853 (x : Nat) : Nat :=
  match Nat.find? (p := fun (t : Nat) => t % 2 = 0 ∠ ∀ (n : Nat), n ∈ Finset.Icc (0 : Nat) x → d853 n ≠ t) with
  | some (t : Nat) => t
  | none => 0
def clause_i : Prop := Filter.Tendsto r853 Filter.atTop Filter.atTop
def clause_ii : Prop := Filter.Tendsto (fun (x : Nat) => ((r853 x : Nat) : ℝ) / Real.log x) Filter.atTop Filter.atTop
def branchA : Prop := (clause_ii → clause_i) ∧ clause_i ∧ clause_ii
def branchB : Prop := ¬ branchA

theorem msl_erdos853_a_m05_c1 : branchA ∨ branchB := by sorry
