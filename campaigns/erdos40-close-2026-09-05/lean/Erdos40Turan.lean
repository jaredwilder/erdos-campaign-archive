/-
  Erdős Problem 40 — the FLOOR: any single answer function settles Erdős–Turán.

  The source page (erdosproblems.com/40) remarks that Erdős 40 "is a stronger form of the
  Erdős–Turán conjecture [28] (since establishing this for ANY function g(N) → ∞ would imply
  a positive solution to [28])".  The upstream formalisation only records the weaker fact
  that `Erdos40ForSet Set.univ` implies Erdős 28 (instantiating at the trivial `g = √N`).

  This file kernel-checks the remark as stated: ONE function `g` that is eventually `≥ 1`
  and lies in the answer set already yields Erdős–Turán.  The bridge is the elementary
  counting bound `|A ∩ [1,N]| ≫ √N` for any additive basis of order 2.

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Erdos40Core

namespace Erdos40

open Finset Filter Set Asymptotics
open scoped Topology Pointwise

attribute [local instance 100] Classical.propDecidable

/-- `|A ∩ [0,N]| ≤ |A ∩ [1,N]| + 1`: the two counting conventions differ by the point `0`. -/
theorem cnt_zero_le (A : Set ℕ) (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun a => a ∈ A)).card ≤ cnt A N + 1 := by
  classical
  have hsub : (Finset.range (N + 1)).filter (fun a => a ∈ A) ⊆
      insert 0 ((Finset.Icc 1 N).filter (fun a => a ∈ A)) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    rcases Nat.eq_zero_or_pos x with rfl | hpos
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, by omega⟩, hx.2⟩)
  calc ((Finset.range (N + 1)).filter (fun a => a ∈ A)).card
      ≤ (insert 0 ((Finset.Icc 1 N).filter (fun a => a ∈ A))).card := Finset.card_le_card hsub
    _ ≤ ((Finset.Icc 1 N).filter (fun a => a ∈ A)).card + 1 := Finset.card_insert_le _ _
    _ = cnt A N + 1 := rfl

/-- **Basis counting bound.**  If `A + A` omits only finitely many naturals then there is a
constant `M` with `N - M ≤ (|A ∩ [1,N]| + 1)²` for every `N`: every `n ∈ (M, N]` is a sum of
two elements of `A ∩ [0,N]`, and there are at most `(|A ∩ [1,N]| + 1)²` such sums. -/
theorem basis_count {A : Set ℕ} (hA : (A + A)ᶜ.Finite) :
    ∃ M : ℕ, ∀ N : ℕ, N - M ≤ (cnt A N + 1) * (cnt A N + 1) := by
  classical
  obtain ⟨M, hM⟩ := hA.bddAbove
  refine ⟨M, fun N => ?_⟩
  set S : Finset (ℕ × ℕ) :=
    ((Finset.range (N + 1)).filter (fun a => a ∈ A)) ×ˢ
    ((Finset.range (N + 1)).filter (fun a => a ∈ A)) with hS
  have hsurj : Set.SurjOn (fun p : ℕ × ℕ => p.1 + p.2) (↑S) (↑(Finset.Icc (M + 1) N)) := by
    intro n hn
    rw [Finset.mem_coe, Finset.mem_Icc] at hn
    have hnot : n ∉ (A + A)ᶜ := by
      intro hmem
      have := hM hmem
      omega
    have hnot' : n ∈ A + A := by
      by_contra hcon
      exact hnot hcon
    obtain ⟨a, ha, b, hb, hab⟩ := hnot'
    have hab' : a + b = n := hab
    refine ⟨(a, b), ?_, hab'⟩
    rw [Finset.mem_coe, hS, Finset.mem_product]
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb⟩
  have hcard : (Finset.Icc (M + 1) N).card ≤ S.card :=
    Finset.card_le_card_of_surjOn _ hsurj
  have hIcc : (Finset.Icc (M + 1) N).card = N - M := by
    rw [Nat.card_Icc]; omega
  have hSc : S.card = ((Finset.range (N + 1)).filter (fun a => a ∈ A)).card *
      ((Finset.range (N + 1)).filter (fun a => a ∈ A)).card := by
    rw [hS, Finset.card_product]
  have hle := cnt_zero_le A N
  calc N - M = (Finset.Icc (M + 1) N).card := hIcc.symm
    _ ≤ S.card := hcard
    _ = ((Finset.range (N + 1)).filter (fun a => a ∈ A)).card *
        ((Finset.range (N + 1)).filter (fun a => a ∈ A)).card := hSc
    _ ≤ (cnt A N + 1) * (cnt A N + 1) := Nat.mul_le_mul hle hle

/-- **`√N ≤ 3 |A ∩ [1,N]|` eventually, for any additive basis of order 2.** -/
theorem sqrt_le_three_mul_cnt {A : Set ℕ} (hA : (A + A)ᶜ.Finite) :
    ∀ᶠ N : ℕ in atTop, Real.sqrt (N : ℝ) ≤ 3 * (cnt A N : ℝ) := by
  obtain ⟨M, hM⟩ := basis_count hA
  filter_upwards [eventually_ge_atTop (2 * M + 4)] with N hN
  have hbase := hM N
  set c := cnt A N with hc
  have hcpos : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0] at hbase; omega
    · exact h0
  have hstep : (c + 1) * (c + 1) ≤ (2 * c) * (2 * c) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hNat : N ≤ 9 * (c * c) := by
    have h1 : N ≤ 2 * (N - M) := by omega
    have h2 : N - M ≤ (2 * c) * (2 * c) := le_trans hbase hstep
    have h3 : (2 * c) * (2 * c) = 4 * (c * c) := by ring
    omega
  have hR : (N : ℝ) ≤ (3 * (c : ℝ)) ^ 2 := by
    have : ((N : ℕ) : ℝ) ≤ ((9 * (c * c) : ℕ) : ℝ) := by exact_mod_cast hNat
    push_cast at this
    nlinarith [this]
  calc Real.sqrt (N : ℝ) ≤ Real.sqrt ((3 * (c : ℝ)) ^ 2) := Real.sqrt_le_sqrt hR
    _ = 3 * (c : ℝ) := Real.sqrt_sq (by positivity)

/-- **THE FLOOR.**  If a single `g` that is eventually `≥ 1` belongs to the answer set of
Erdős 40, then the Erdős–Turán conjecture (Erdős Problem 28) holds: every additive basis of
order 2 has an unbounded representation function.

This is the source page's own remark, kernel-checked, and is strictly stronger than the
upstream `erdos_40.variants.implies_erdos_28`, which assumes the statement for ALL `g`. -/
theorem erdos28_of_erdos40For {g : ℕ → ℝ} (hg : ∀ᶠ N : ℕ in atTop, 1 ≤ g N)
    (H : Erdos40For g) {A : Set ℕ} (hA : (A + A)ᶜ.Finite) :
    limsup (fun n : ℕ => (rep A n : ℕ∞)) atTop = ⊤ := by
  refine H A ?_
  refine IsBigO.of_bound 3 ?_
  filter_upwards [hg, sqrt_le_three_mul_cnt hA] with N h1 h2
  have hs : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hdiv : Real.sqrt (N : ℝ) / g N ≤ Real.sqrt (N : ℝ) := div_le_self hs h1
  have hdivnn : (0 : ℝ) ≤ Real.sqrt (N : ℝ) / g N :=
    div_nonneg hs (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hdivnn,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ((A ∩ Set.Icc 1 N).ncard : ℝ)), ncard_eq_cnt]
  linarith

/-- **Restated:** the answer set of Erdős 40 is nonempty (among functions eventually `≥ 1`)
only if Erdős–Turán is true.  Together with `Erdos40.answer_set_ceiling`, the answer set is
trapped between an open $500 conjecture below and an explicit kernel-checked ceiling above. -/
theorem erdos28_of_exists_answer
    (h : ∃ g : ℕ → ℝ, (∀ᶠ N : ℕ in atTop, 1 ≤ g N) ∧ Erdos40For g) :
    ∀ A : Set ℕ, (A + A)ᶜ.Finite → limsup (fun n : ℕ => (rep A n : ℕ∞)) atTop = ⊤ := by
  obtain ⟨g, hg, H⟩ := h
  exact fun A hA => erdos28_of_erdos40For hg H hA

end Erdos40
