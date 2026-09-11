/-
# Erdős Problem 3 — the Erdős–Turán conjecture on arithmetic progressions ($5,000)

Statement (erdosproblems.com/3, FormalConjectures `ErdosProblems/3.lean`):
if `A ⊆ ℕ` has `∑_{n ∈ A} 1/n = ∞` then `A` contains arbitrarily long arithmetic progressions.

STATUS OF THE PROBLEM: OPEN for progressions of length `k ≥ 4`.
`k = 3` is a theorem of Bloom–Sisask (2020), which is NOT formalized in Mathlib.

WHAT THIS FILE PROVES (all sorry-free, kernel-checked):

* `summable_recip_iff` — the DYADIC CHARACTERIZATION.  `∑_{n ∈ A} 1/n` converges iff
  `∑_j |A ∩ [2^j, 2^{j+1})| / 2^j` converges.  This is an exact reformulation of the
  hypothesis of Erdős 3 as a statement about dyadic densities.
* `summable_of_dyadic_count_bound` — abstract density transfer.
* `summable_of_log_power_bound` — the DENSITY TRANSFER THEOREM.  If the counting function
  of `A` satisfies `|A ∩ [0,N)| ≤ C·N/(log N)^{1+ε}` for some `ε > 0` and all large `N`,
  then `∑_{n ∈ A} 1/n` converges.  Contrapositive: a divergent reciprocal sum FORCES the
  counting function above `N/(log N)^{1+ε}` infinitely often, for every `ε > 0`.
* `erdos3_of_quantSzemeredi` — THE REDUCTION.  A quantitative Szemerédi bound
  `r_k(N) ≪ N/(log N)^{1+ε}` implies Erdős 3 for progressions of length `k`.
* `frequently_hasAP_iff_forall` — formalization-fidelity: the `∃ᶠ k in atTop` shape used in
  the FormalConjectures statement is equivalent to `∀ k`.
* `divergent_forces_density` — the explicit contrapositive, stated for the record.

WHAT IS *NOT* PROVED HERE: the conjecture itself.  `QuantSzemeredi k` is a hypothesis;
for `k = 3` it is Bloom–Sisask's theorem (unformalized), for `k ≥ 4` it is open.

Author: Oracle estate, campaign `erdos3-close-2026-09-05`.
Compiled against Mathlib rev 919544d4309104b3f19724b0e6e48c701d27948f, Lean v4.31.0-rc1.
-/

import Mathlib

open Finset Filter

namespace Erdos3

/-! ## Definitions

We use real-valued counting functions built from `Set.indicator`, which avoids all
decidability side-conditions while being definitionally the cardinality. -/

/-- Real-valued indicator of `A`. -/
noncomputable def ind (A : Set ℕ) : ℕ → ℝ := Set.indicator A fun _ => (1 : ℝ)

/-- `n ↦ 1/n` supported on `A`.  Note `recip A 0 = 0` since `(0:ℝ)⁻¹ = 0`. -/
noncomputable def recip (A : Set ℕ) : ℕ → ℝ := Set.indicator A fun n => 1 / (n : ℝ)

/-- The counting function `|A ∩ [0,N)|`, as a real number. -/
noncomputable def count (A : Set ℕ) (N : ℕ) : ℝ := ∑ i ∈ range N, ind A i

/-- `|A ∩ [2^j, 2^(j+1))|`, as a real number. -/
noncomputable def blockCount (A : Set ℕ) (j : ℕ) : ℝ := ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)), ind A i

/-- `∑_{n ∈ A ∩ [2^j, 2^(j+1))} 1/n`. -/
noncomputable def blockSum (A : Set ℕ) (j : ℕ) : ℝ := ∑ i ∈ Ico (2 ^ j) (2 ^ (j + 1)), recip A i

/-! ## Elementary facts -/

lemma ind_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ ind A n :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) n

lemma recip_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ recip A n :=
  Set.indicator_nonneg (fun a _ => by positivity) n

lemma recip_eq (A : Set ℕ) (n : ℕ) : recip A n = ind A n * (1 / (n : ℝ)) := by
  unfold recip ind
  by_cases h : n ∈ A <;> simp [Set.indicator_apply, h]

lemma recip_zero (A : Set ℕ) : recip A 0 = 0 := by
  simp [recip_eq]

lemma count_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ count A N :=
  Finset.sum_nonneg fun i _ => ind_nonneg A i

lemma blockCount_nonneg (A : Set ℕ) (j : ℕ) : 0 ≤ blockCount A j :=
  Finset.sum_nonneg fun i _ => ind_nonneg A i

lemma blockSum_nonneg (A : Set ℕ) (j : ℕ) : 0 ≤ blockSum A j :=
  Finset.sum_nonneg fun i _ => recip_nonneg A i

lemma blockCount_le_count (A : Set ℕ) (j : ℕ) : blockCount A j ≤ count A (2 ^ (j + 1)) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ind_nonneg A i)
  intro i hi
  rw [Finset.mem_Ico] at hi
  exact Finset.mem_range.2 hi.2

/-! ## The dyadic block estimates -/

/-- On the block `[2^j, 2^(j+1))` every reciprocal is at most `2^{-j}`. -/
lemma blockSum_le (A : Set ℕ) (j : ℕ) : blockSum A j ≤ blockCount A j / 2 ^ j := by
  unfold blockSum blockCount
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  have hpow : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hile : ((2 : ℝ) ^ j) ≤ (i : ℝ) := by exact_mod_cast hi.1
  have hi0 : (0 : ℝ) < (i : ℝ) := lt_of_lt_of_le hpow hile
  have h1 : (1 : ℝ) / (i : ℝ) ≤ 1 / (2 : ℝ) ^ j := by
    exact one_div_le_one_div_of_le hpow hile
  have hrw : ind A i / (2 : ℝ) ^ j = ind A i * (1 / (2 : ℝ) ^ j) := by ring
  rw [recip_eq, hrw]
  exact mul_le_mul_of_nonneg_left h1 (ind_nonneg A i)

/-- On the block `[2^j, 2^(j+1))` every reciprocal is at least `2^{-(j+1)}`. -/
lemma le_blockSum (A : Set ℕ) (j : ℕ) : blockCount A j / 2 ^ (j + 1) ≤ blockSum A j := by
  unfold blockSum blockCount
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  have hpow : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hile : ((2 : ℝ) ^ j) ≤ (i : ℝ) := by exact_mod_cast hi.1
  have hi0 : (0 : ℝ) < (i : ℝ) := lt_of_lt_of_le hpow hile
  have hiub : (i : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
    have : (i : ℝ) < (2 : ℝ) ^ (j + 1) := by exact_mod_cast hi.2
    linarith
  have h1 : (1 : ℝ) / (2 : ℝ) ^ (j + 1) ≤ 1 / (i : ℝ) :=
    one_div_le_one_div_of_le hi0 hiub
  have hrw : ind A i / (2 : ℝ) ^ (j + 1) = ind A i * (1 / (2 : ℝ) ^ (j + 1)) := by ring
  rw [recip_eq, hrw]
  exact mul_le_mul_of_nonneg_left h1 (ind_nonneg A i)

/-! ## Dyadic decomposition of the partial sums -/

lemma dyadic_split (A : Set ℕ) :
    ∀ J : ℕ, ∑ i ∈ Ico 1 (2 ^ J), recip A i = ∑ j ∈ range J, blockSum A j := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
      have h1 : (1 : ℕ) ≤ 2 ^ J := Nat.one_le_two_pow
      have h2 : (2 : ℕ) ^ J ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)
      rw [Finset.sum_range_succ, ← ih, ← Finset.sum_Ico_consecutive (recip A) h1 h2]
      rfl

lemma sum_range_two_pow (A : Set ℕ) (J : ℕ) :
    ∑ i ∈ range (2 ^ J), recip A i = ∑ j ∈ range J, blockSum A j := by
  rw [← dyadic_split A J, Finset.range_eq_Ico]
  have h1 : (0 : ℕ) ≤ 1 := Nat.zero_le 1
  have h2 : (1 : ℕ) ≤ 2 ^ J := Nat.one_le_two_pow
  rw [← Finset.sum_Ico_consecutive (recip A) h1 h2]
  simp [recip_zero]

/-! ## The dyadic characterization of divergence

This is the exact reformulation of the hypothesis of Erdős Problem 3. -/

/-- **Dyadic characterization.**  `∑_{n ∈ A} 1/n` converges if and only if the series of
dyadic densities `∑_j |A ∩ [2^j, 2^{j+1})| / 2^j` converges. -/
theorem summable_recip_iff (A : Set ℕ) :
    Summable (recip A) ↔ Summable fun j : ℕ => blockCount A j / 2 ^ j := by
  constructor
  · intro hs
    have key : ∀ J : ℕ, ∑ j ∈ range J, blockCount A j / 2 ^ (j + 1) ≤ ∑' i, recip A i := by
      intro J
      calc ∑ j ∈ range J, blockCount A j / 2 ^ (j + 1)
          ≤ ∑ j ∈ range J, blockSum A j := Finset.sum_le_sum fun j _ => le_blockSum A j
        _ = ∑ i ∈ range (2 ^ J), recip A i := (sum_range_two_pow A J).symm
        _ ≤ ∑' i, recip A i := hs.sum_le_tsum _ fun i _ => recip_nonneg A i
    have h2 : Summable fun j : ℕ => blockCount A j / 2 ^ (j + 1) :=
      summable_of_sum_range_le
        (fun j => div_nonneg (blockCount_nonneg A j) (by positivity)) key
    have h3 := h2.mul_left 2
    refine h3.congr fun j => ?_
    have : ((2 : ℝ) ^ (j + 1)) = 2 * 2 ^ j := by ring
    rw [this]
    field_simp
  · intro hs
    refine summable_of_sum_range_le (c := ∑' j, blockCount A j / 2 ^ j)
      (fun n => recip_nonneg A n) fun N => ?_
    have hNle : N ≤ 2 ^ N := Nat.le_of_lt Nat.lt_two_pow_self
    have hsub : range N ⊆ range (2 ^ N) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    calc ∑ i ∈ range N, recip A i
        ≤ ∑ i ∈ range (2 ^ N), recip A i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => recip_nonneg A i)
      _ = ∑ j ∈ range N, blockSum A j := sum_range_two_pow A N
      _ ≤ ∑ j ∈ range N, blockCount A j / 2 ^ j :=
          Finset.sum_le_sum fun j _ => blockSum_le A j
      _ ≤ ∑' j, blockCount A j / 2 ^ j :=
          hs.sum_le_tsum _ fun j _ => div_nonneg (blockCount_nonneg A j) (by positivity)

/-! ## Density transfer -/

/-- Abstract density transfer: a summable dyadic counting series forces convergence. -/
theorem summable_of_dyadic_count_bound (A : Set ℕ)
    (h : Summable fun j : ℕ => count A (2 ^ (j + 1)) / 2 ^ j) : Summable (recip A) := by
  rw [summable_recip_iff]
  refine Summable.of_nonneg_of_le
    (fun j => div_nonneg (blockCount_nonneg A j) (by positivity)) (fun j => ?_) h
  gcongr
  exact blockCount_le_count A j

/-- **Density transfer theorem.**  If the counting function of `A` is eventually bounded by
`C·N/(log N)^{1+ε}` for some `ε > 0`, then `∑_{n ∈ A} 1/n` converges.

Equivalently (contrapositive): if `∑_{n ∈ A} 1/n = ∞` then for every `ε > 0` the counting
function of `A` exceeds `N/(log N)^{1+ε}` infinitely often. -/
theorem summable_of_log_power_bound (A : Set ℕ) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (N₀ : ℕ) (h : ∀ N : ℕ, N₀ ≤ N → count A N ≤ C * (N : ℝ) / (Real.log N) ^ (1 + ε)) :
    Summable (recip A) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := 2 * C / (Real.log 2) ^ (1 + ε) with hK
  have hKnn : 0 ≤ K := by
    have : (0 : ℝ) < (Real.log 2) ^ (1 + ε) := Real.rpow_pos_of_pos hlog2 _
    positivity
  -- the comparison series
  have hcomp : Summable fun j : ℕ => K / ((j : ℝ) + 1) ^ (1 + ε) := by
    have hps : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + ε) :=
      Real.summable_one_div_nat_rpow.2 (by linarith)
    have hsh : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 + ε) := by
      have := (summable_nat_add_iff 1).2 hps
      simpa using this
    simpa [div_eq_mul_inv, mul_comm] using hsh.mul_left K
  apply summable_of_dyadic_count_bound
  rw [← summable_nat_add_iff N₀]
  refine Summable.of_nonneg_of_le
    (fun j => div_nonneg (count_nonneg A _) (by positivity))
    (fun j => ?_) ((summable_nat_add_iff N₀).2 hcomp)
  -- the pointwise bound on the tail
  set m := j + N₀ with hm
  have hNle : N₀ ≤ 2 ^ (m + 1) := by
    calc N₀ ≤ 2 ^ N₀ := Nat.le_of_lt Nat.lt_two_pow_self
      _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb := h (2 ^ (m + 1)) hNle
  have hcast : (((2 : ℕ) ^ (m + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (m + 1) := by push_cast; ring
  rw [hcast] at hb
  have hlogpow : Real.log ((2 : ℝ) ^ (m + 1)) = ((m : ℝ) + 1) * Real.log 2 := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlogpow] at hb
  have hden : (((m : ℝ) + 1) * Real.log 2) ^ (1 + ε)
      = ((m : ℝ) + 1) ^ (1 + ε) * (Real.log 2) ^ (1 + ε) :=
    Real.mul_rpow (by positivity) (le_of_lt hlog2)
  rw [hden] at hb
  have hm1 : (0 : ℝ) < ((m : ℝ) + 1) ^ (1 + ε) := Real.rpow_pos_of_pos (by positivity) _
  have hl1 : (0 : ℝ) < (Real.log 2) ^ (1 + ε) := Real.rpow_pos_of_pos hlog2 _
  have hpow : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hne1 : ((m : ℝ) + 1) ^ (1 + ε) ≠ 0 := ne_of_gt hm1
  have hne2 : (Real.log 2) ^ (1 + ε) ≠ 0 := ne_of_gt hl1
  -- the bound : count / 2^m ≤ K / (m+1)^(1+ε)
  rw [div_le_iff₀ hpow]
  have heq : K / ((m : ℝ) + 1) ^ (1 + ε) * 2 ^ m
      = C * (2 : ℝ) ^ (m + 1) / (((m : ℝ) + 1) ^ (1 + ε) * (Real.log 2) ^ (1 + ε)) := by
    rw [hK]; field_simp; ring
  rw [heq]
  exact hb

/-- The contrapositive, stated for the record: a divergent reciprocal sum forces the counting
function above `N/(log N)^{1+ε}` at arbitrarily large `N`, for every `ε > 0` and every `C`. -/
theorem divergent_forces_density (A : Set ℕ) (hdiv : ¬ Summable (recip A))
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) :
    ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ C * (N : ℝ) / (Real.log N) ^ (1 + ε) < count A N := by
  intro N₀
  by_contra hcon
  push_neg at hcon
  exact hdiv (summable_of_log_power_bound A hε hC N₀ fun N hN => hcon N hN)

/-! ## Arithmetic progressions and the reduction -/

/-- `A` contains an arithmetic progression of length `k`. -/
def HasAPOfLength (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

lemma hasAPOfLength_mono (A : Set ℕ) {k l : ℕ} (hkl : l ≤ k) (h : HasAPOfLength A k) :
    HasAPOfLength A l := by
  obtain ⟨a, d, hd, hmem⟩ := h
  exact ⟨a, d, hd, fun i hi => hmem i (lt_of_lt_of_le hi hkl)⟩

/-- Formalization fidelity: the `∃ᶠ k in atTop` shape used by the FormalConjectures
statement of Erdős 3 is equivalent to the `∀ k` shape. -/
theorem frequently_hasAP_iff_forall (A : Set ℕ) :
    (∃ᶠ k in Filter.atTop, HasAPOfLength A k) ↔ ∀ k, HasAPOfLength A k := by
  constructor
  · intro hfreq k
    obtain ⟨l, hl, hAP⟩ := (Filter.frequently_atTop.1 hfreq) k
    exact hasAPOfLength_mono A hl hAP
  · intro hall
    exact Filter.Frequently.of_forall fun k => hall k

/-- The quantitative Szemerédi hypothesis at length `k`: every set free of `k`-term
arithmetic progressions has counting function `≪ N/(log N)^{1+ε}`.

This is implied by the standard bound `r_k(N) ≤ C·N/(log N)^{1+ε}` on the size of the largest
`k`-AP-free subset of `[1,N]`.  For `k = 3` it is a theorem of Bloom–Sisask (2020); for
`k ≥ 4` it is open (Gowers gives only `N/(log log N)^{c}`). -/
def QuantSzemeredi (k : ℕ) : Prop :=
  ∃ ε > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Set ℕ,
    ¬ HasAPOfLength S k → count S N ≤ C * (N : ℝ) / (Real.log N) ^ (1 + ε)

/-- **The reduction.**  A quantitative Szemerédi bound with a power of `log` strictly above `1`
implies Erdős Problem 3 for progressions of length `k`. -/
theorem erdos3_of_quantSzemeredi (k : ℕ) (hk : QuantSzemeredi k) (A : Set ℕ)
    (hA : ¬ Summable (recip A)) : HasAPOfLength A k := by
  by_contra hno
  obtain ⟨ε, hε, C, hC, N₀, hbound⟩ := hk
  exact hA (summable_of_log_power_bound A hε hC N₀ fun N hN => hbound N hN A hno)

/-! ## The headline statement, in the shape of FormalConjectures `ErdosProblems/3.lean` -/

lemma summable_subtype_iff (A : Set ℕ) :
    Summable (fun a : A => 1 / (a : ℝ)) ↔ Summable (recip A) :=
  summable_subtype_iff_indicator (f := fun n : ℕ => 1 / (n : ℝ)) (s := A)

/-- **Erdős Problem 3, conditional on quantitative Szemerédi.**  Stated in the exact shape of
the FormalConjectures file, with `∃ᶠ k in atTop` replaced by the equivalent `∀ k`
(see `frequently_hasAP_iff_forall`). -/
theorem erdos3_conditional (h : ∀ k : ℕ, QuantSzemeredi k) :
    ∀ A : Set ℕ, (¬ Summable fun a : A => 1 / (a : ℝ)) →
      ∃ᶠ (k : ℕ) in Filter.atTop, HasAPOfLength A k := by
  intro A hA
  rw [frequently_hasAP_iff_forall]
  intro k
  exact erdos3_of_quantSzemeredi k (h k) A (fun hs => hA ((summable_subtype_iff A).2 hs))

/-- **Erdős Problem 3 for `k = 3`, conditional on Bloom–Sisask.**  `QuantSzemeredi 3` is
exactly the content of Bloom–Sisask, *Breaking the logarithmic barrier in Roth's theorem on
arithmetic progressions* (2020), which is not yet formalized in Mathlib. -/
theorem erdos3_three_of_bloomSisask (h : QuantSzemeredi 3) (A : Set ℕ)
    (hA : ¬ Summable fun a : A => 1 / (a : ℝ)) : HasAPOfLength A 3 :=
  erdos3_of_quantSzemeredi 3 h A (fun hs => hA ((summable_subtype_iff A).2 hs))

end Erdos3
