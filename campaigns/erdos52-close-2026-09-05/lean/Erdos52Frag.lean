/-
Erdos Problem 52 (Erdos-Szemeredi sum-product) -- kernel-checked fragments.

Campaign : erdos52-close-2026-09-05
Frozen formal source : FormalConjectures/ErdosProblems/52.lean
  sha256 ab3530733d90e41c5420f38d2ca52967019299da48d50184f3fd142a6b3eb989
Frozen prose source  : oracle/evidence/formalizer-sources/erdos/raw-erdos-52.html
  sha256 747343f8181c23fba16c1a4ff6667b3bf3e169714813fde05859525f6d017273

This file contains NO sorry. `SumProduct` below is the frozen target predicate and is
NOT proved here; it is DEFINED so that the fragments can be stated against it.
-/
import Mathlib

open scoped Pointwise

namespace Erdos52Frag

/-- The frozen target predicate, transcribed from the RHS of `Erdos52.erdos_52`. -/
def SumProduct : Prop :=
  ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

/-- The sum-only variant of the frozen target (drops the `max`). -/
def SumOnly : Prop :=
  ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    ((A + A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

/-- The product-only variant of the frozen target (drops the `max`). -/
def ProdOnly : Prop :=
  ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ),
    ((A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

/-! ### F1. The degenerate case is vacuous for every constant. -/

theorem empty_holds (ε C : ℝ) (hε : ε < 2) :
    (max ((∅ : Finset ℤ) + ∅).card ((∅ : Finset ℤ) * ∅).card : ℝ)
      ≥ C * ((∅ : Finset ℤ).card : ℝ) ^ (2 - ε) := by
  have h : (2 : ℝ) - ε ≠ 0 := by linarith
  simp [Real.zero_rpow h]

/-! ### F2. The exponent-1 baseline: `|A| <= max(|A+A|,|AA|)`. -/

theorem card_le_card_add {A : Finset ℤ} (hA : A.Nonempty) : A.card ≤ (A + A).card := by
  obtain ⟨a, ha⟩ := hA
  have hinj : Function.Injective (fun x : ℤ => a + x) := fun x y h => by simpa using h
  have hsub : A.image (fun x => a + x) ⊆ A + A := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.add_mem_add ha hx
  calc A.card = (A.image (fun x => a + x)).card :=
        (Finset.card_image_of_injective A hinj).symm
    _ ≤ (A + A).card := Finset.card_le_card hsub

theorem card_le_max {A : Finset ℤ} (hA : A.Nonempty) :
    A.card ≤ max (A + A).card (A * A).card :=
  le_trans (card_le_card_add hA) (le_max_left _ _)

/-! ### F3. Any admissible constant is at most one (the normalisation anchor). -/

theorem const_le_one {ε C : ℝ}
    (h : ∀ (A : Finset ℤ), (max (A + A).card (A * A).card : ℝ)
          ≥ C * (A.card : ℝ) ^ (2 - ε)) : C ≤ 1 := by
  have h1 := h {0}
  have e1 : (({0} : Finset ℤ) + {0}) = {0} := by simp
  have e2 : (({0} : Finset ℤ) * {0}) = {0} := by simp
  rw [e1, e2, Finset.card_singleton] at h1
  simp only [Nat.cast_one, max_self, Real.one_rpow, mul_one] at h1
  linarith

/-! ### F4. The `ε`-family is monotone: a constant for `ε` serves every larger `ε'`. -/

theorem eps_mono {ε ε' C : ℝ} (hle : ε ≤ ε') (hε' : ε' < 2) (hC : 0 ≤ C) (A : Finset ℤ)
    (H : (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)) :
    (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε') := by
  refine le_trans ?_ H
  rcases Nat.eq_zero_or_pos A.card with h0 | h0
  · have hx : ((A.card : ℝ)) = 0 := by rw [h0]; norm_num
    have hne : (2 : ℝ) - ε' ≠ 0 := by linarith
    have hne2 : (2 : ℝ) - ε ≠ 0 := by linarith
    rw [hx, Real.zero_rpow hne, Real.zero_rpow hne2]
  · have hx : (1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast h0
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hC

/-! ### F5. The growth lemma behind the `max`-necessity refutations. -/

theorem exists_beats {ε C : ℝ} (hε : ε < 1) (hC : 0 < C) :
    ∃ n : ℕ, 0 < n ∧ (2 * n : ℝ) < C * (n : ℝ) ^ (2 - ε) := by
  have hpos : (0 : ℝ) < 1 - ε := by linarith
  have ht : Filter.Tendsto (fun x : ℝ => x ^ (1 - ε)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hpos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((Filter.tendsto_atTop.mp ht) (2 / C + 1))
  obtain ⟨m, hm⟩ := exists_nat_ge N
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  have hn2 : N ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hnpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have h1 : 2 / C + 1 ≤ ((m + 1 : ℕ) : ℝ) ^ (1 - ε) := hN _ hn2
  have h2 : 2 / C < ((m + 1 : ℕ) : ℝ) ^ (1 - ε) := by linarith
  have hrw : ((m + 1 : ℕ) : ℝ) ^ (2 - ε)
      = ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ^ (1 - ε) := by
    rw [show (2 : ℝ) - ε = 1 + (1 - ε) by ring, Real.rpow_add hnpos, Real.rpow_one]
  rw [hrw]
  have hmul : C * (2 / C) < C * (((m + 1 : ℕ) : ℝ) ^ (1 - ε)) :=
    mul_lt_mul_of_pos_left h2 hC
  have hcc : C * (2 / C) = 2 := by field_simp
  have h5 : (2 : ℝ) < C * (((m + 1 : ℕ) : ℝ) ^ (1 - ε)) := by linarith
  have h6 : 2 * ((m + 1 : ℕ) : ℝ)
      < (C * (((m + 1 : ℕ) : ℝ) ^ (1 - ε))) * ((m + 1 : ℕ) : ℝ) :=
    mul_lt_mul_of_pos_right h5 hnpos
  have h7 : (C * (((m + 1 : ℕ) : ℝ) ^ (1 - ε))) * ((m + 1 : ℕ) : ℝ)
      = C * (((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ^ (1 - ε)) := by ring
  rw [← h7]
  exact h6

/-! ### F6. The arithmetic-progression family: linear sumset. -/

/-- `AP n = {0, 1, ..., n-1}` as a finite set of integers. -/
def AP (n : ℕ) : Finset ℤ := (Finset.range n).image (fun i : ℕ => (i : ℤ))

theorem card_AP (n : ℕ) : (AP n).card = n := by
  have hinj : Function.Injective (fun i : ℕ => (i : ℤ)) :=
    fun a b h => Int.ofNat_inj.mp h
  rw [AP, Finset.card_image_of_injective _ hinj, Finset.card_range]

theorem AP_add_subset (n : ℕ) :
    AP n + AP n ⊆ (Finset.range (2 * n)).image (fun i : ℕ => (i : ℤ)) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  simp only [Finset.mem_range] at hi hj
  refine Finset.mem_image.mpr ⟨i + j, ?_, by push_cast; ring⟩
  simp only [Finset.mem_range]
  omega

theorem card_AP_add (n : ℕ) : (AP n + AP n).card ≤ 2 * n := by
  calc (AP n + AP n).card
      ≤ ((Finset.range (2 * n)).image (fun i : ℕ => (i : ℤ))).card :=
        Finset.card_le_card (AP_add_subset n)
    _ ≤ (Finset.range (2 * n)).card := Finset.card_image_le
    _ = 2 * n := Finset.card_range _

/-! ### F7. The geometric-progression family: linear product set. -/

theorem two_pow_strictMono : StrictMono (fun i : ℕ => (2 : ℤ) ^ i) :=
  strictMono_nat_of_lt_succ (fun n => by
    have h : (0 : ℤ) < 2 ^ n := by positivity
    simp only [pow_succ]
    linarith)

/-- `GP n = {2^0, ..., 2^(n-1)}` as a finite set of integers. -/
def GP (n : ℕ) : Finset ℤ := (Finset.range n).image (fun i => (2 : ℤ) ^ i)

theorem card_GP (n : ℕ) : (GP n).card = n := by
  rw [GP, Finset.card_image_of_injective _ two_pow_strictMono.injective, Finset.card_range]

theorem GP_mul_subset (n : ℕ) :
    GP n * GP n ⊆ (Finset.range (2 * n)).image (fun i => (2 : ℤ) ^ i) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  simp only [Finset.mem_range] at hi hj
  refine Finset.mem_image.mpr ⟨i + j, ?_, by rw [pow_add]⟩
  simp only [Finset.mem_range]
  omega

theorem card_GP_mul (n : ℕ) : (GP n * GP n).card ≤ 2 * n := by
  calc (GP n * GP n).card
      ≤ ((Finset.range (2 * n)).image (fun i => (2 : ℤ) ^ i)).card :=
        Finset.card_le_card (GP_mul_subset n)
    _ ≤ (Finset.range (2 * n)).card := Finset.card_image_le
    _ = 2 * n := Finset.card_range _

/-! ### F8. `max` is load-bearing: neither one-sided variant is true. -/

theorem not_sumOnly : ¬ SumOnly := by
  intro h
  obtain ⟨C, hC, hA⟩ := h (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨n, hn, hlt⟩ := exists_beats (ε := (1 / 2 : ℝ)) (by norm_num) hC
  have h1 := hA (AP n)
  rw [card_AP] at h1
  have h2 : ((AP n + AP n).card : ℝ) ≤ 2 * (n : ℝ) := by
    have := card_AP_add n
    exact_mod_cast this
  linarith

theorem not_prodOnly : ¬ ProdOnly := by
  intro h
  obtain ⟨C, hC, hA⟩ := h (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨n, hn, hlt⟩ := exists_beats (ε := (1 / 2 : ℝ)) (by norm_num) hC
  have h1 := hA (GP n)
  rw [card_GP] at h1
  have h2 : ((GP n * GP n).card : ℝ) ≤ 2 * (n : ℝ) := by
    have := card_GP_mul n
    exact_mod_cast this
  linarith

/-- Both terms of the `max` in the frozen statement are necessary. -/
theorem max_is_necessary : ¬ SumOnly ∧ ¬ ProdOnly := ⟨not_sumOnly, not_prodOnly⟩

end Erdos52Frag

#print axioms Erdos52Frag.empty_holds
#print axioms Erdos52Frag.card_le_max
#print axioms Erdos52Frag.const_le_one
#print axioms Erdos52Frag.eps_mono
#print axioms Erdos52Frag.exists_beats
#print axioms Erdos52Frag.card_AP
#print axioms Erdos52Frag.card_AP_add
#print axioms Erdos52Frag.card_GP
#print axioms Erdos52Frag.card_GP_mul
#print axioms Erdos52Frag.not_sumOnly
#print axioms Erdos52Frag.not_prodOnly
#print axioms Erdos52Frag.max_is_necessary
