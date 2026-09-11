/-
  Erdős Problem 28 — the COUNTING SANDWICH on a hypothetical counterexample.

  Kernel-checked, sorry-free: a set `A` that is simultaneously an additive basis of order 2
  and has `r_A ≤ B` has counting function pinned on BOTH sides,

      √(N − M)  ≤  |A ∩ [0,N]|  ≤  √(B(2N+1)),

  i.e. `|A ∩ [0,N]| ≍ √N`.  The lower pin is the basis hypothesis (every large `n ≤ N` is a
  sum of two elements of `A ∩ [0,N]`); the upper pin is the bounded representation function
  (the pairs of sum `≤ N` are counted twice, once by `A`'s square and once by `∑ r_A`).

  Reused, with credit and unchanged proofs, from the sibling campaigns:
    * `erdos66-close-2026-09-05/lean/Erdos66Core.lean` — `pairsLe`, `pairsLe_eq_biUnion`,
      `sum_rep_eq`, `sum_rep_le`, `le_sum_rep` (the `counting_sandwich` machinery).
    * `erdos40-close-2026-09-05/lean/Erdos40Turan.lean` — `basis_count` (restated here in
      the `[0,N]` window, which removes the `+1` slack of the `[1,N]` version).

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Erdos28Parity

namespace Erdos28

open Finset Filter Set
open scoped Topology Pointwise

attribute [local instance 100] Classical.propDecidable

/-- All ordered pairs from `A` with sum at most `N`. -/
noncomputable def pairsLe (A : Set ℕ) (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
    (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 ≤ N)

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

/-! ## The lower pin: the basis hypothesis -/

/-- **Basis counting bound.**  If `A + A` omits only finitely many naturals then there is an
`M` with `N − M ≤ |A ∩ [0,N]|²` for every `N`: every `n ∈ (M, N]` is a sum of two elements of
`A ∩ [0,N]`, and there are at most `|A ∩ [0,N]|²` such sums. -/
theorem basis_count {A : Set ℕ} (hA : IsBasis2 A) :
    ∃ M : ℕ, ∀ N : ℕ, N - M ≤ cnt A N * cnt A N := by
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
  have hSc : S.card = cnt A N * cnt A N := by
    rw [hS, Finset.card_product]; rfl
  calc N - M = (Finset.Icc (M + 1) N).card := hIcc.symm
    _ ≤ S.card := hcard
    _ = cnt A N * cnt A N := hSc

/-! ## The upper pin: a bounded representation function -/

/-- **Bounded-representation counting bound.**  If `r_A(n) ≤ B` for every `n` then
`|A ∩ [0,N]|² ≤ B(2N+1)` for every `N`. -/
theorem cnt_sq_le_of_rep_le {A : Set ℕ} {B : ℕ} (hB : ∀ n, rep A n ≤ B) (N : ℕ) :
    cnt A N * cnt A N ≤ B * (2 * N + 1) := by
  have hlow := le_sum_rep A (2 * N)
  have hdiv : 2 * N / 2 = N := by omega
  rw [hdiv] at hlow
  have hsum : ∑ n ∈ Finset.range (2 * N + 1), rep A n ≤ B * (2 * N + 1) := by
    calc ∑ n ∈ Finset.range (2 * N + 1), rep A n
        ≤ ∑ _n ∈ Finset.range (2 * N + 1), B := Finset.sum_le_sum (fun n _ => hB n)
      _ = B * (2 * N + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
  exact le_trans hlow hsum

/-! ## The sandwich -/

/-- **THE SANDWICH (natural-number form).**  A hypothetical counterexample to Erdős–Turán —
an additive basis of order 2 with `r_A ≤ B` — has its counting function trapped between
`√(N−M)` and `√(B(2N+1))`, and its bound satisfies `2 ≤ B`. -/
theorem counterexample_sandwich {A : Set ℕ} {B : ℕ} (hA : IsBasis2 A) (hB : ∀ n, rep A n ≤ B) :
    2 ≤ B ∧ ∃ M : ℕ, ∀ N : ℕ,
      N - M ≤ cnt A N * cnt A N ∧ cnt A N * cnt A N ≤ B * (2 * N + 1) := by
  refine ⟨two_le_bound_of_basis hA hB, ?_⟩
  obtain ⟨M, hM⟩ := basis_count hA
  exact ⟨M, fun N => ⟨hM N, cnt_sq_le_of_rep_le hB N⟩⟩

/-- **THE SANDWICH (real form).**  Explicitly `√(N − M) ≤ |A ∩ [0,N]| ≤ √(B(2N+1))`, so the
counting function of any counterexample is `Θ(√N)`. -/
theorem counterexample_sandwich_real {A : Set ℕ} {B : ℕ}
    (hA : IsBasis2 A) (hB : ∀ n, rep A n ≤ B) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      Real.sqrt ((N : ℝ) - (M : ℝ)) ≤ (cnt A N : ℝ) ∧
      (cnt A N : ℝ) ≤ Real.sqrt ((B : ℝ) * (2 * (N : ℝ) + 1)) := by
  obtain ⟨M, hM⟩ := basis_count hA
  refine ⟨M, fun N hMN => ⟨?_, ?_⟩⟩
  · have hnat := hM N
    have hcast : ((N : ℝ) - (M : ℝ)) ≤ ((cnt A N : ℝ)) ^ 2 := by
      have h1 : ((N - M : ℕ) : ℝ) ≤ ((cnt A N * cnt A N : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [Nat.cast_sub hMN] at h1
      push_cast at h1
      nlinarith [h1]
    calc Real.sqrt ((N : ℝ) - (M : ℝ))
        ≤ Real.sqrt (((cnt A N : ℝ)) ^ 2) := Real.sqrt_le_sqrt hcast
      _ = (cnt A N : ℝ) := Real.sqrt_sq (by positivity)
  · have hnat := cnt_sq_le_of_rep_le hB N
    have hcast : ((cnt A N : ℝ)) ^ 2 ≤ (B : ℝ) * (2 * (N : ℝ) + 1) := by
      have h1 : ((cnt A N * cnt A N : ℕ) : ℝ) ≤ ((B * (2 * N + 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at h1
      nlinarith [h1]
    calc (cnt A N : ℝ) = Real.sqrt (((cnt A N : ℝ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((B : ℝ) * (2 * (N : ℝ) + 1)) := Real.sqrt_le_sqrt hcast

end Erdos28
