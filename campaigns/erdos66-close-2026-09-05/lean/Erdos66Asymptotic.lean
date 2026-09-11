/-
  Erdős Problem 66 — the counting-function consequence of a hypothetical witness.

  Building on `Erdos66Core`, this file proves sorry-free that if `A ⊆ ℕ` satisfies
  `r_A(n)/log n → c`, then the counting function `cnt A` is pinned to order
  `sqrt(N log N)` from BOTH sides.  This is a necessary condition on any witness for
  Erdős 66; it does not resolve the problem.

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Erdos66Core

namespace Erdos66

open Finset Filter
open scoped Topology

attribute [local instance 100] Classical.propDecidable

private lemma log_nat_nonneg (n : ℕ) : (0 : ℝ) ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

private lemma log_nat_mono {m n : ℕ} (h : m ≤ n) : Real.log m ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simpa [hm] using log_nat_nonneg n
  · have h0 : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 : (m : ℝ) ≤ n := by exact_mod_cast h
    exact Real.log_le_log h0 h1

theorem nonneg_of_tendsto {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => (rep A n : ℝ) / Real.log n) atTop (𝓝 c)) : 0 ≤ c := by
  have hev : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ (rep A n : ℝ) / Real.log n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds h hev

/-- **A uniform termwise bound.**  A witness with limit `c` has `r_A(n) ≤ M + (c+1) log n`
for *every* `n`, with a single constant `M` absorbing the finitely many small `n`. -/
theorem exists_uniform_rep_bound {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => (rep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, (rep A n : ℝ) ≤ M + (c + 1) * Real.log n := by
  have hc0 : 0 ≤ c := nonneg_of_tendsto h
  have hev : ∀ᶠ n : ℕ in atTop, (rep A n : ℝ) / Real.log n < c + 1 :=
    h.eventually (gt_mem_nhds (by linarith))
  obtain ⟨n₀, hn₀⟩ := (hev.and (eventually_ge_atTop 2)).exists_forall_of_atTop
  refine ⟨((Finset.range n₀).sup (fun n => rep A n) : ℕ), by positivity, fun n => ?_⟩
  by_cases hlt : n < n₀
  · have h1 : rep A n ≤ (Finset.range n₀).sup (fun n => rep A n) :=
      Finset.le_sup (Finset.mem_range.mpr hlt)
    have h2 : (0 : ℝ) ≤ (c + 1) * Real.log n :=
      mul_nonneg (by linarith) (log_nat_nonneg n)
    have h3 : (rep A n : ℝ) ≤ ((Finset.range n₀).sup (fun n => rep A n) : ℕ) := by
      exact_mod_cast h1
    linarith
  · push_neg at hlt
    obtain ⟨hb, h2n⟩ := hn₀ n hlt
    have hpos : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast h2n)
    have : (rep A n : ℝ) < (c + 1) * Real.log n := by
      rw [div_lt_iff₀ hpos] at hb
      linarith
    have hM : (0 : ℝ) ≤ ((Finset.range n₀).sup (fun n => rep A n) : ℕ) := by positivity
    linarith

/-- The partial sums of `r_A` are `O(N log N)` for any witness. -/
theorem sum_rep_le_of_tendsto {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => (rep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      ((∑ n ∈ Finset.range (N + 1), rep A n : ℕ) : ℝ)
        ≤ (N + 1) * M + (c + 1) * ((N + 1) * Real.log N) := by
  obtain ⟨M, hM, hb⟩ := exists_uniform_rep_bound h
  have hc0 : 0 ≤ c := nonneg_of_tendsto h
  refine ⟨M, hM, fun N => ?_⟩
  have step1 : ((∑ n ∈ Finset.range (N + 1), rep A n : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.range (N + 1), (M + (c + 1) * Real.log N) := by
    push_cast
    refine Finset.sum_le_sum ?_
    intro n hn
    refine (hb n).trans ?_
    have : Real.log n ≤ Real.log N := log_nat_mono (by
      have := Finset.mem_range.mp hn; omega)
    have hc1 : (0 : ℝ) ≤ c + 1 := by linarith
    nlinarith [this, hc1]
  calc ((∑ n ∈ Finset.range (N + 1), rep A n : ℕ) : ℝ)
      ≤ ∑ _n ∈ Finset.range (N + 1), (M + (c + 1) * Real.log N) := step1
    _ = (N + 1) * (M + (c + 1) * Real.log N) := by
        rw [Finset.sum_const, Finset.card_range]; ring
    _ = (N + 1) * M + (c + 1) * ((N + 1) * Real.log N) := by ring

/-- **UPPER BOUND: any witness for Erdős 66 is sparse.**
`cnt A (N/2)^2 = O(N log N)`, i.e. the counting function of any witness is
`O(sqrt(N log N))`. -/
theorem cnt_sq_le_of_tendsto {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => (rep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ,
      (cnt A (N / 2) : ℝ) ^ 2 ≤ (N + 1) * M + (c + 1) * ((N + 1) * Real.log N) := by
  obtain ⟨M, hM, hb⟩ := sum_rep_le_of_tendsto h
  refine ⟨M, hM, fun N => ?_⟩
  have h1 : cnt A (N / 2) * cnt A (N / 2) ≤ ∑ n ∈ Finset.range (N + 1), rep A n :=
    le_sum_rep A N
  calc (cnt A (N / 2) : ℝ) ^ 2
      = ((cnt A (N / 2) * cnt A (N / 2) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((∑ n ∈ Finset.range (N + 1), rep A n : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ _ := hb N

/-- **LOWER BOUND: any witness with `c > 0` is dense enough.**
Eventually `(N/2) * (c/2) * log (N/2) ≤ cnt A N ^ 2`, i.e. the counting function of any
witness is `≫ sqrt(N log N)`. -/
theorem le_cnt_sq_of_tendsto {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => (rep A n : ℝ) / Real.log n) atTop (𝓝 c)) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      ((N / 2 : ℕ) : ℝ) * ((c / 2) * Real.log ((N / 2 : ℕ) : ℝ)) ≤ (cnt A N : ℝ) ^ 2 := by
  have hev : ∀ᶠ n : ℕ in atTop, c / 2 < (rep A n : ℝ) / Real.log n :=
    h.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n₀, hn₀⟩ := (hev.and (eventually_ge_atTop 2)).exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop (2 * n₀ + 4)] with N hN
  -- every `x` in `[N/2, N]` is `≥ n₀` and `≥ 2`
  have hkey : ∀ x ∈ Finset.Ico (N / 2) (N + 1),
      (c / 2) * Real.log ((N / 2 : ℕ) : ℝ) ≤ (rep A x : ℝ) := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    have hxn₀ : n₀ ≤ x := by omega
    have hx2 : 2 ≤ x := by omega
    obtain ⟨hb, -⟩ := hn₀ x hxn₀
    have hpos : (0 : ℝ) < Real.log x := Real.log_pos (by exact_mod_cast hx2)
    have hstep : (c / 2) * Real.log x ≤ (rep A x : ℝ) := by
      rw [lt_div_iff₀ hpos] at hb
      linarith
    have hmono : Real.log ((N / 2 : ℕ) : ℝ) ≤ Real.log x := log_nat_mono hx.1
    nlinarith [hmono, hc.le, hpos]
  -- sum over the window, then over the whole range, then apply the sandwich
  have hcard : (Finset.Ico (N / 2) (N + 1)).card = N + 1 - N / 2 := by
    rw [Nat.card_Ico]
  have hwin : ((Finset.Ico (N / 2) (N + 1)).card : ℝ) *
      ((c / 2) * Real.log ((N / 2 : ℕ) : ℝ))
      ≤ ∑ x ∈ Finset.Ico (N / 2) (N + 1), (rep A x : ℝ) := by
    have := Finset.card_nsmul_le_sum (Finset.Ico (N / 2) (N + 1))
      (fun x => (rep A x : ℝ)) ((c / 2) * Real.log ((N / 2 : ℕ) : ℝ)) hkey
    simpa [nsmul_eq_mul] using this
  have hsub : ∑ x ∈ Finset.Ico (N / 2) (N + 1), (rep A x : ℝ)
      ≤ ∑ x ∈ Finset.range (N + 1), (rep A x : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro x hx
    rw [Finset.mem_Ico] at hx
    exact Finset.mem_range.mpr (by omega)
  have hsand : ∑ x ∈ Finset.range (N + 1), (rep A x : ℝ) ≤ (cnt A N : ℝ) ^ 2 := by
    have := sum_rep_le A N
    have hcast : ((∑ n ∈ Finset.range (N + 1), rep A n : ℕ) : ℝ) ≤ (cnt A N : ℝ) ^ 2 := by
      calc ((∑ n ∈ Finset.range (N + 1), rep A n : ℕ) : ℝ)
          ≤ ((cnt A N * cnt A N : ℕ) : ℝ) := by exact_mod_cast this
        _ = (cnt A N : ℝ) ^ 2 := by push_cast; ring
    simpa using hcast
  have hlow : ((N / 2 : ℕ) : ℝ) ≤ ((Finset.Ico (N / 2) (N + 1)).card : ℝ) := by
    rw [hcard]
    have : N / 2 ≤ N + 1 - N / 2 := by omega
    exact_mod_cast this
  have hnn : (0 : ℝ) ≤ (c / 2) * Real.log ((N / 2 : ℕ) : ℝ) :=
    mul_nonneg (by linarith) (log_nat_nonneg _)
  calc ((N / 2 : ℕ) : ℝ) * ((c / 2) * Real.log ((N / 2 : ℕ) : ℝ))
      ≤ ((Finset.Ico (N / 2) (N + 1)).card : ℝ) *
        ((c / 2) * Real.log ((N / 2 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hlow hnn
    _ ≤ ∑ x ∈ Finset.Ico (N / 2) (N + 1), (rep A x : ℝ) := hwin
    _ ≤ ∑ x ∈ Finset.range (N + 1), (rep A x : ℝ) := hsub
    _ ≤ (cnt A N : ℝ) ^ 2 := hsand

end Erdos66
