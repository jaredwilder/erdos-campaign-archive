/-
Erdős Problem 20 — the Sunflower Conjecture.

ATTACK 06: an IMPROVED lower bound base for k = 3.

Erdős–Rado's product construction gives `(k-1)^n < f n k`, i.e. base 2 at k = 3.
The multiplier of Attack05 turns any single better seed into a better base.
Here the seed is the 6-edge graph "two disjoint triangles" on `Fin 6`: a
2-uniform family of SIX sets with no 3-sunflower, against `(k-1)^n = 4`.
(No vertex has degree 3, so no 3-star; no 3 pairwise disjoint edges, so no
empty-kernel sunflower; three distinct 2-sets cannot share a 2-element kernel.)
Verified by kernel `decide` over the full 64-subset powerset.

Squaring it t times:

    (3-1)^(2t) = 4^t  <  6^t  <  f (2t) 3.

so the lower-bound base for k = 3 improves from 2 to √6 ≈ 2.449.
-/
import Mathlib
import Attack01
import Attack02
import Attack03
import Attack04
import Attack05

set_option maxHeartbeats 2000000
set_option maxRecDepth 40000

namespace Erdos20Prod

open Erdos20Corpus Erdos20Lower

/-- An explicit `k`-sunflower-free `n`-uniform family of size at least `M`,
on SOME ground type. -/
def HasWitness (n k M : ℕ) : Prop :=
  ∃ (γ : Type) (F : Set (Set γ)),
    (∀ A ∈ F, A.ncard = n) ∧ M ≤ F.ncard ∧
      (∀ S ⊆ F, S.ncard = k → ¬ IsSunflower S)

theorem HasWitness.lower {n k M : ℕ} (h : HasWitness n k M) (hn : 0 < n) :
    M < f n k := by
  obtain ⟨γ, F, huni, hM, hfree⟩ := h
  exact lower_of_witness (α := γ) n k M hn F huni hM hfree

/-- **Witnesses multiply.** -/
theorem HasWitness.mul {n₁ n₂ k M₁ M₂ : ℕ} (hk : 2 ≤ k) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (h₁ : HasWitness n₁ k M₁) (h₂ : HasWitness n₂ k M₂) :
    HasWitness (n₁ + n₂) k (M₁ * M₂) := by
  obtain ⟨γ₁, F₁, huni₁, hM₁, hfree₁⟩ := h₁
  obtain ⟨γ₂, F₂, huni₂, hM₂, hfree₂⟩ := h₂
  refine ⟨γ₁ ⊕ γ₂, prodFam F₁ F₂, prodFam_uniform hn₁ hn₂ huni₁ huni₂, ?_,
    prodFam_free hk hn₁ huni₁ huni₂ hfree₁ hfree₂⟩
  rw [prodFam_ncard]
  exact Nat.mul_le_mul hM₁ hM₂

/-! ### Bridge: an explicit Finset family is a witness -/

instance instDecIsSunflowerF {γ : Type} [DecidableEq γ] [Fintype γ]
    (S : Finset (Finset γ)) : Decidable (Erdos20Attack.IsSunflowerF S) := by
  unfold Erdos20Attack.IsSunflowerF Erdos20Attack.SunflowerWithKernel
  infer_instance

theorem hasWitness_of_finset {γ : Type} [DecidableEq γ] {n k M : ℕ} (hk : 2 ≤ k)
    (Fs : Finset (Finset γ))
    (huni : ∀ s ∈ Fs, s.card = n)
    (hM : M ≤ Fs.card)
    (hfree : ∀ T ⊆ Fs, T.card = k → ¬ Erdos20Attack.IsSunflowerF T) :
    HasWitness n k M := by
  classical
  refine ⟨γ, (fun s : Finset γ => (↑s : Set γ)) '' (↑Fs : Set (Finset γ)), ?_, ?_, ?_⟩
  · rintro A ⟨s, hs, rfl⟩
    rw [Set.ncard_coe_finset]
    exact huni s (Finset.mem_coe.mp hs)
  · rw [Set.InjOn.ncard_image (Finset.coe_injective.injOn), Set.ncard_coe_finset]
    exact hM
  · rintro S hS hScard ⟨C, hC⟩
    set T : Finset (Finset γ) := Fs.filter (fun s => (↑s : Set γ) ∈ S) with hT
    have hTFs : T ⊆ Fs := by rw [hT]; exact Finset.filter_subset _ _
    have hTmem : ∀ s, s ∈ T ↔ (s ∈ Fs ∧ (↑s : Set γ) ∈ S) := by
      intro s; rw [hT]; exact Finset.mem_filter
    have hSeq : S = (fun s : Finset γ => (↑s : Set γ)) '' (↑T : Set (Finset γ)) := by
      ext X
      constructor
      · intro hX
        obtain ⟨s, hs, rfl⟩ := hS hX
        exact ⟨s, Finset.mem_coe.mpr ((hTmem s).mpr ⟨Finset.mem_coe.mp hs, hX⟩), rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ((hTmem s).mp (Finset.mem_coe.mp hs)).2
    have hTcard : T.card = k := by
      rw [hSeq, Set.InjOn.ncard_image (Finset.coe_injective.injOn),
        Set.ncard_coe_finset] at hScard
      exact hScard
    -- two distinct members give a Finset kernel
    have h2 : ∃ s ∈ T, ∃ t ∈ T, s ≠ t := Finset.one_lt_card.mp (by omega)
    obtain ⟨s₀, hs₀, t₀, ht₀, hst⟩ := h2
    have hmemS : ∀ s ∈ T, (↑s : Set γ) ∈ S := fun s hs => ((hTmem s).mp hs).2
    have hCK : C = (↑(s₀ ∩ t₀) : Set γ) := by
      rw [Finset.coe_inter]
      exact (hC (hmemS s₀ hs₀) (hmemS t₀ ht₀)
        (fun h => hst (Finset.coe_injective h))).symm
    refine hfree T hTFs hTcard ⟨s₀ ∩ t₀, ?_⟩
    intro A hA B hB hAB
    have hne : (↑A : Set γ) ≠ (↑B : Set γ) := fun h => hAB (Finset.coe_injective h)
    have := hC (hmemS A hA) (hmemS B hB) hne
    rw [hCK] at this
    rw [← Finset.coe_inter] at this
    exact Finset.coe_injective this

/-! ### The seed: two disjoint triangles -/

/-- Two disjoint triangles on `Fin 6`: six 2-sets, no 3-sunflower. -/
def seedFs : Finset (Finset (Fin 6)) :=
  {{0, 1}, {1, 2}, {0, 2}, {3, 4}, {4, 5}, {3, 5}}

theorem seed_uniform : ∀ s ∈ seedFs, s.card = 2 := by decide

theorem seed_card : 6 ≤ seedFs.card := by decide

theorem seed_free : ∀ T ⊆ seedFs, T.card = 3 → ¬ Erdos20Attack.IsSunflowerF T := by decide

theorem seed_witness : HasWitness 2 3 6 :=
  hasWitness_of_finset (by norm_num) seedFs seed_uniform seed_card seed_free

/-! ### Iterating the seed -/

theorem witness_pow : ∀ t : ℕ, 0 < t → HasWitness (2 * t) 3 (6 ^ t) := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · simpa using seed_witness
      · have hprev := ih htpos
        have := HasWitness.mul (k := 3) (by norm_num) (by omega) (by norm_num) hprev seed_witness
        have harith : 2 * t + 2 = 2 * (t + 1) := by ring
        have hpow : 6 ^ t * 6 = 6 ^ (t + 1) := by ring
        rw [harith, hpow] at this
        exact this

/-- **Improved lower bound for `k = 3`:** `6^t < f (2t) 3`. -/
theorem lower_k3 (t : ℕ) (ht : 0 < t) : 6 ^ t < f (2 * t) 3 :=
  (witness_pow t ht).lower (by omega)

/-- The Erdős–Rado product bound at `k = 3, n = 2t` is `4^t`; the seeded bound `6^t`
strictly beats it. -/
theorem beats_erdos_rado_product (t : ℕ) (ht : 0 < t) :
    (3 - 1) ^ (2 * t) < 6 ^ t := by
  have h : (3 - 1) ^ (2 * t) = 4 ^ t := by
    norm_num [pow_mul]
  rw [h]
  exact Nat.pow_lt_pow_left (by norm_num) (by omega)

/-- **The first genuinely unknown case, narrowed.** `6 < f 2 3 ≤ 9`.
The Erdős–Rado sandwich alone gives only `4 < f 2 3 ≤ 9`; the seed raises the
floor to 7.  (The true value is 7; the matching upper bound `f 2 3 ≤ 7` is NOT
proved here.) -/
theorem f_two_three : 6 < f 2 3 ∧ f 2 3 ≤ 9 := by
  refine ⟨seed_witness.lower (by norm_num), ?_⟩
  have h := erdos_rado_bound 2 3 (by norm_num) (by norm_num)
  norm_num [Nat.factorial] at h
  exact h

end Erdos20Prod

#print axioms Erdos20Prod.f_two_three
#print axioms Erdos20Prod.hasWitness_of_finset
#print axioms Erdos20Prod.seed_free
#print axioms Erdos20Prod.seed_witness
#print axioms Erdos20Prod.lower_k3
#print axioms Erdos20Prod.beats_erdos_rado_product
