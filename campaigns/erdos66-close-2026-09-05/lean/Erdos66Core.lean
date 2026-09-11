/-
  Erdős Problem 66 — kernel-checked structural core.

  Target (OPEN, $500, erdosproblems.com/66):
      Is there `A ⊆ ℕ` with `lim_{n→∞} (1_A * 1_A)(n) / log n` existing and `≠ 0`?

  THIS FILE DOES NOT CLOSE THAT PROBLEM.  It proves, sorry-free, elementary structural
  facts that every hypothetical witness must satisfy, and binds the definition used here
  to the upstream `sumRep` of google-deepmind/formal-conjectures.

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Mathlib

namespace Erdos66

open Finset Filter
open scoped Topology

attribute [local instance 100] Classical.propDecidable

/-- `rep A n` is the number of ORDERED pairs `(a, b) ∈ A × A` with `a + b = n`.
This is `(1_A ∗ 1_A) n`; see `rep_eq_sumConv` for the binding to the upstream
`sumRep` of the formal-conjectures statement of Erdős 66. -/
noncomputable def rep (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)).card

/-- `cnt A x = |A ∩ [0, x]|`, the counting function of `A`. -/
noncomputable def cnt (A : Set ℕ) (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun a => a ∈ A)).card

/-- All ordered pairs from `A` with sum at most `N`. -/
noncomputable def pairsLe (A : Set ℕ) (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
    (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 ≤ N)

/-! ## Semantic binding to the upstream statement -/

/-- **Binding lemma.**  `rep` is literally the upstream `sumRep A n = (𝟙_A ∗ 𝟙_A) n`,
i.e. `∑ p ∈ antidiagonal n, 1_A p.1 * 1_A p.2`.  This is the guard against a
formal/prose mismatch: everything below is a statement about the object named in the
formalised Erdős 66. -/
theorem rep_eq_sumConv (A : Set ℕ) (n : ℕ) :
    rep A n = ∑ p ∈ Finset.antidiagonal n,
      (Set.indicator A (fun _ => (1 : ℕ)) p.1) * (Set.indicator A (fun _ => (1 : ℕ)) p.2) := by
  rw [rep, Finset.card_filter]
  refine Finset.sum_congr rfl ?_
  intro p _
  by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ A <;>
    simp [h1, h2]

/-! ## The exact partial-sum identity -/

theorem pairsLe_eq_biUnion (A : Set ℕ) (N : ℕ) :
    pairsLe A N =
      (Finset.range (N + 1)).biUnion
        (fun n => (Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)) := by
  ext p
  constructor
  · intro hp
    simp only [pairsLe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨-, hA1, hA2, hle⟩ := hp
    refine Finset.mem_biUnion.mpr ⟨p.1 + p.2, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr rfl, hA1, hA2⟩
  · intro hp
    obtain ⟨n, hn, hp⟩ := Finset.mem_biUnion.mp hp
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    rw [Finset.mem_range] at hn
    obtain ⟨hsum, hA1, hA2⟩ := hp
    simp only [pairsLe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, hA1, hA2, by omega⟩

/-- **Exact identity.**  `∑_{n ≤ N} r_A(n)` counts the ordered pairs from `A` of sum `≤ N`. -/
theorem sum_rep_eq (A : Set ℕ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), rep A n = (pairsLe A N).card := by
  rw [pairsLe_eq_biUnion, Finset.card_biUnion]
  · rfl
  · intro x _ y _ hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hpx hpy
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at hpx hpy
    apply hxy
    rw [← hpx.1]
    exact hpy.1

/-! ## The counting-function sandwich

For every `A` and every `N`,
  `cnt A (N/2)^2  ≤  ∑_{n ≤ N} r_A(n)  ≤  cnt A N ^ 2`.
This is the elementary two-sided bridge between the representation function and the
counting function of `A`. -/

theorem sum_rep_le (A : Set ℕ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), rep A n ≤ cnt A N * cnt A N := by
  rw [sum_rep_eq]
  have hsub : pairsLe A N ⊆
      ((Finset.range (N + 1)).filter (fun a => a ∈ A)) ×ˢ
      ((Finset.range (N + 1)).filter (fun a => a ∈ A)) := by
    intro p hp
    simp only [pairsLe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    tauto
  calc (pairsLe A N).card
      ≤ (((Finset.range (N + 1)).filter (fun a => a ∈ A)) ×ˢ
         ((Finset.range (N + 1)).filter (fun a => a ∈ A))).card := Finset.card_le_card hsub
    _ = cnt A N * cnt A N := by rw [Finset.card_product]; rfl

theorem le_sum_rep (A : Set ℕ) (N : ℕ) :
    cnt A (N / 2) * cnt A (N / 2) ≤ ∑ n ∈ Finset.range (N + 1), rep A n := by
  rw [sum_rep_eq]
  have hsub :
      ((Finset.range (N / 2 + 1)).filter (fun a => a ∈ A)) ×ˢ
      ((Finset.range (N / 2 + 1)).filter (fun a => a ∈ A)) ⊆ pairsLe A N := by
    intro p hp
    simp only [pairsLe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    obtain ⟨⟨h1, hA1⟩, h2, hA2⟩ := hp
    exact ⟨⟨by omega, by omega⟩, hA1, hA2, by omega⟩
  calc cnt A (N / 2) * cnt A (N / 2)
      = (((Finset.range (N / 2 + 1)).filter (fun a => a ∈ A)) ×ˢ
         ((Finset.range (N / 2 + 1)).filter (fun a => a ∈ A))).card := by
        rw [Finset.card_product]; rfl
    _ ≤ (pairsLe A N).card := Finset.card_le_card hsub

/-- **The sandwich**, both sides together. -/
theorem counting_sandwich (A : Set ℕ) (N : ℕ) :
    cnt A (N / 2) * cnt A (N / 2) ≤ ∑ n ∈ Finset.range (N + 1), rep A n ∧
    ∑ n ∈ Finset.range (N + 1), rep A n ≤ cnt A N * cnt A N :=
  ⟨le_sum_rep A N, sum_rep_le A N⟩

/-! ## Necessary conditions on any witness -/

theorem rep_le_of_finite {A : Set ℕ} (hA : A.Finite) (n : ℕ) :
    rep A n ≤ hA.toFinset.card * hA.toFinset.card := by
  have hsub : ((Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A))
      ⊆ hA.toFinset ×ˢ hA.toFinset := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_product]
    exact ⟨hA.mem_toFinset.mpr hp.2.1, hA.mem_toFinset.mpr hp.2.2⟩
  calc rep A n ≤ (hA.toFinset ×ˢ hA.toFinset).card := Finset.card_le_card hsub
    _ = hA.toFinset.card * hA.toFinset.card := Finset.card_product _ _

/-- **Any witness has a positive limit.**  The Erdős 66 statement asks only for `c ≠ 0`;
since `r_A` is a cardinality and `log n > 0` eventually, `c ≠ 0` forces `c > 0`. -/
theorem pos_of_tendsto {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => (rep A n : ℝ) / Real.log n) atTop (𝓝 c)) (hc : c ≠ 0) :
    0 < c := by
  have hev : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ (rep A n : ℝ) / Real.log n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
  have h0 : (0 : ℝ) ≤ c := le_of_tendsto_of_tendsto tendsto_const_nhds h hev
  exact lt_of_le_of_ne h0 (Ne.symm hc)

/-- **Any witness is infinite.**  A finite `A` has bounded `r_A`, so `r_A(n)/log n → 0`. -/
theorem infinite_of_tendsto {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => (rep A n : ℝ) / Real.log n) atTop (𝓝 c)) (hc : c ≠ 0) :
    A.Infinite := by
  by_contra hcon
  rw [Set.not_infinite] at hcon
  set K : ℝ := (hcon.toFinset.card : ℝ) * (hcon.toFinset.card : ℝ) with hKdef
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hKlim : Tendsto (fun n : ℕ => K / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hlow : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ (rep A n : ℝ) / Real.log n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
  have hhigh : ∀ᶠ n : ℕ in atTop, (rep A n : ℝ) / Real.log n ≤ K / Real.log n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have hnum : (rep A n : ℝ) ≤ K := by
      rw [hKdef]
      exact_mod_cast rep_le_of_finite hcon n
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hpos.le)
  have hzero : Tendsto (fun n : ℕ => (rep A n : ℝ) / Real.log n) atTop (𝓝 0) :=
    squeeze_zero' hlow hhigh hKlim
  exact hc (tendsto_nhds_unique h hzero)

end Erdos66
