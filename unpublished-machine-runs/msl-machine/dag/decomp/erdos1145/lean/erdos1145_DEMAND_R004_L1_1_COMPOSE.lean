import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def SeqStrict (f : ℕ → ℕ) : Prop := ∀ n : ℕ, 1 ≤ f n ∧ f n < f (n + 1)

def sumsetMem (a b : ℕ → ℕ) (m : ℕ) : Prop := ∃ i j : ℕ, a i + b j = m

def convAB (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n).filter
    (fun p : ℕ × ℕ => a p.1 + b p.2 = n)).card

theorem msl_erdos1145_demand_r004_l1_1_composition : ((∀ (a : ℕ → ℕ) (b : ℕ → ℕ), ∀ (a b : ℕ → ℕ), SeqStrict a → SeqStrict b → ∀ m : ℕ, 2 ≤ m →
 sumsetMem a b m → ∃ i j : ℕ, i < m ∧ j < m ∧ a i + b j = m) ∧ (∀ (a : ℕ → ℕ) (b : ℕ → ℕ), ∀ (a b : ℕ → ℕ), SeqStrict a → SeqStrict b →
 (Filter.Tendsto (fun n : ℕ => ((a n : ℚ) / (b n : ℚ))) Filter.atTop (nhds (1 : ℚ)) ↔
  Filter.Tendsto (fun n : ℕ => (((a n : ℚ) - (b n : ℚ)) / (b n : ℚ))) Filter.atTop (nhds (0 : ℚ)))) ∧ (∀ (a : ℕ → ℕ) (b : ℕ → ℕ), ∀ (a b : ℕ → ℕ),
 ((∀ k : ℕ, {n : ℕ | k ≤ convAB a b n}.Infinite) ↔
  ∀ k : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ k ≤ convAB a b n))) → (∀ (a b : ℕ → ℕ), SeqStrict a → SeqStrict b →
 Filter.Tendsto (fun n : ℕ => ((a n : ℚ) / (b n : ℚ))) Filter.atTop (nhds (1 : ℚ)) →
 (∃ N : ℕ, ∀ m : ℕ, N ≤ m → sumsetMem a b m) →
 (∀ k : ℕ, {n : ℕ | k ≤ convAB a b n}.Infinite)) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos1145_demand_r004_l1_1_composition
