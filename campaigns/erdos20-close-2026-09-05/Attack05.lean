/-
Erdős Problem 20 — the Sunflower Conjecture.

ATTACK 05: **sunflower-free families MULTIPLY.**

If `F₁` is a `k`-sunflower-free `n₁`-uniform family of size `M₁` and `F₂` is a
`k`-sunflower-free `n₂`-uniform family of size `M₂` (on disjoint ground sets),
then `{A ⊔ B : A ∈ F₁, B ∈ F₂}` is a `k`-sunflower-free `(n₁+n₂)`-uniform family
of size `M₁ · M₂`.  Hence

    M₁ * M₂  <  f (n₁ + n₂) k.

This is the lower-bound multiplier: ANY single improved seed `M > (k-1)^n` at one
value of `n` propagates to `M^(1/n)` as the base of the lower bound for all large
`n`.  Attack03's `(k-1)^n` is the degenerate case seeded at `n = 1`.

The proof rests on a dichotomy: in a sunflower inside the product family, the
left projections are either ALL distinct (a sunflower in `F₁`) or ALL equal
(forcing a sunflower in `F₂`).  Nothing in between is possible.
-/
import Mathlib
import Attack01
import Attack02
import Attack03
import Attack04

namespace Erdos20Prod

open Erdos20Corpus Erdos20Lower

variable {α β : Type}

/-! ### The disjoint union of two sets -/

def prodSet (A : Set α) (B : Set β) : Set (α ⊕ β) := Sum.inl '' A ∪ Sum.inr '' B

def pi1 (X : Set (α ⊕ β)) : Set α := Sum.inl ⁻¹' X
def pi2 (X : Set (α ⊕ β)) : Set β := Sum.inr ⁻¹' X

lemma pi1_inter (X Y : Set (α ⊕ β)) : pi1 (X ∩ Y) = pi1 X ∩ pi1 Y := Set.preimage_inter
lemma pi2_inter (X Y : Set (α ⊕ β)) : pi2 (X ∩ Y) = pi2 X ∩ pi2 Y := Set.preimage_inter

lemma pi1_mono {X Y : Set (α ⊕ β)} (h : X ⊆ Y) : pi1 X ⊆ pi1 Y := Set.preimage_mono h

lemma pi1_prodSet (A : Set α) (B : Set β) : pi1 (prodSet A B) = A := by
  rw [pi1, prodSet, Set.preimage_union, Set.preimage_image_eq _ Sum.inl_injective]
  simp

lemma pi2_prodSet (A : Set α) (B : Set β) : pi2 (prodSet A B) = B := by
  rw [pi2, prodSet, Set.preimage_union, Set.preimage_image_eq _ Sum.inr_injective]
  simp

lemma prodSet_disjoint (A : Set α) (B : Set β) :
    Disjoint (Sum.inl '' A) (Sum.inr '' B) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, _, rfl⟩ ⟨b, _, hb⟩
  simp at hb

lemma prodSet_ncard {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    (prodSet A B).ncard = A.ncard + B.ncard := by
  rw [prodSet, Set.ncard_union_eq (prodSet_disjoint A B) (hA.image _) (hB.image _),
    Set.InjOn.ncard_image (Sum.inl_injective.injOn),
    Set.InjOn.ncard_image (Sum.inr_injective.injOn)]

lemma prodSet_inj {A₁ A₂ : Set α} {B₁ B₂ : Set β}
    (h : prodSet A₁ B₁ = prodSet A₂ B₂) : A₁ = A₂ ∧ B₁ = B₂ := by
  refine ⟨?_, ?_⟩
  · rw [← pi1_prodSet A₁ B₁, ← pi1_prodSet A₂ B₂, h]
  · rw [← pi2_prodSet A₁ B₁, ← pi2_prodSet A₂ B₂, h]

/-! ### The product family -/

def prodFam (F₁ : Set (Set α)) (F₂ : Set (Set β)) : Set (Set (α ⊕ β)) :=
  (fun p : Set α × Set β => prodSet p.1 p.2) '' (F₁ ×ˢ F₂)

lemma prodFam_ncard (F₁ : Set (Set α)) (F₂ : Set (Set β)) :
    (prodFam F₁ F₂).ncard = F₁.ncard * F₂.ncard := by
  have hinj : Set.InjOn (fun p : Set α × Set β => prodSet p.1 p.2) (F₁ ×ˢ F₂) := by
    rintro ⟨A₁, B₁⟩ _ ⟨A₂, B₂⟩ _ h
    obtain ⟨e1, e2⟩ := prodSet_inj h
    exact Prod.ext e1 e2
  rw [prodFam, hinj.ncard_image, Set.ncard_prod]

lemma prodFam_rec {F₁ : Set (Set α)} {F₂ : Set (Set β)} :
    ∀ X ∈ prodFam F₁ F₂, prodSet (pi1 X) (pi2 X) = X ∧ pi1 X ∈ F₁ ∧ pi2 X ∈ F₂ := by
  rintro X ⟨⟨A, B⟩, ⟨hA, hB⟩, rfl⟩
  rw [pi1_prodSet, pi2_prodSet]
  exact ⟨rfl, hA, hB⟩

lemma prodFam_uniform {F₁ : Set (Set α)} {F₂ : Set (Set β)} {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (h1 : ∀ A ∈ F₁, A.ncard = n₁) (h2 : ∀ B ∈ F₂, B.ncard = n₂) :
    ∀ X ∈ prodFam F₁ F₂, X.ncard = n₁ + n₂ := by
  rintro X ⟨⟨A, B⟩, ⟨hA, hB⟩, rfl⟩
  have hAf : A.Finite := by
    by_contra h
    have h0 := Set.Infinite.ncard h
    have := h1 A hA
    omega
  have hBf : B.Finite := by
    by_contra h
    have h0 := Set.Infinite.ncard h
    have := h2 B hB
    omega
  rw [prodSet_ncard hAf hBf, h1 A hA, h2 B hB]

/-! ### The dichotomy -/

theorem prodFam_free {F₁ : Set (Set α)} {F₂ : Set (Set β)} {n₁ n₂ k : ℕ}
    (hk : 2 ≤ k) (hn₁ : 0 < n₁)
    (h1 : ∀ A ∈ F₁, A.ncard = n₁) (_h2 : ∀ B ∈ F₂, B.ncard = n₂)
    (hf1 : ∀ S ⊆ F₁, S.ncard = k → ¬ IsSunflower S)
    (hf2 : ∀ S ⊆ F₂, S.ncard = k → ¬ IsSunflower S) :
    ∀ S ⊆ prodFam F₁ F₂, S.ncard = k → ¬ IsSunflower S := by
  rintro S hS hScard ⟨C, hC⟩
  classical
  have hSfin : S.Finite := by
    by_contra h
    have h0 := Set.Infinite.ncard h
    omega
  have hrec : ∀ X ∈ S, prodSet (pi1 X) (pi2 X) = X ∧ pi1 X ∈ F₁ ∧ pi2 X ∈ F₂ :=
    fun X hX => prodFam_rec X (hS hX)
  have hker1 : ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → pi1 X ∩ pi1 Y = pi1 C := by
    intro X hX Y hY hXY
    rw [← pi1_inter, hC hX hY hXY]
  have hker2 : ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → pi2 X ∩ pi2 Y = pi2 C := by
    intro X hX Y hY hXY
    rw [← pi2_inter, hC hX hY hXY]
  by_cases hinj : Set.InjOn pi1 S
  · -- ALL left projections distinct: a k-sunflower inside F₁
    refine hf1 (pi1 '' S) ?_ ?_ ⟨pi1 C, ?_⟩
    · rintro A ⟨X, hX, rfl⟩
      exact (hrec X hX).2.1
    · rw [hinj.ncard_image, hScard]
    · rintro A ⟨X, hX, rfl⟩ B ⟨Y, hY, rfl⟩ hAB
      have hXY : X ≠ Y := by rintro rfl; exact hAB rfl
      exact hker1 X hX Y hY hXY
  · -- two left projections coincide: then ALL of them do
    have hcoll : ∃ X ∈ S, ∃ Y ∈ S, pi1 X = pi1 Y ∧ X ≠ Y := by
      by_contra hcon
      push_neg at hcon
      exact hinj (fun X hX Y hY h => hcon X hX Y hY h)
    obtain ⟨X₀, hX₀, Y₀, hY₀, heq, hne⟩ := hcoll
    have hCX : pi1 C = pi1 X₀ := by
      rw [← hker1 X₀ hX₀ Y₀ hY₀ hne, ← heq, Set.inter_self]
    have hconst : ∀ Z ∈ S, pi1 Z = pi1 X₀ := by
      intro Z hZ
      have hW : ∃ W ∈ S, W ≠ Z := by
        by_contra hcon
        push_neg at hcon
        have hle : S.ncard ≤ 1 :=
          (Set.ncard_le_one hSfin).mpr
            (fun a ha b hb => by rw [hcon a ha, hcon b hb])
        omega
      obtain ⟨W, hWS, hWZ⟩ := hW
      have hsub : pi1 X₀ ⊆ pi1 Z := by
        rw [← hCX, ← hC hZ hWS (Ne.symm hWZ), pi1_inter]
        exact Set.inter_subset_left
      have hcard0 : (pi1 X₀).ncard = n₁ := h1 _ (hrec X₀ hX₀).2.1
      have hcardZ : (pi1 Z).ncard = n₁ := h1 _ (hrec Z hZ).2.1
      have hZfin : (pi1 Z).Finite := by
        by_contra hinf
        have h0 := Set.Infinite.ncard hinf
        omega
      exact (Set.eq_of_subset_of_ncard_le hsub (by omega) hZfin).symm
    -- so the RIGHT projections are all distinct: a k-sunflower inside F₂
    have hinj2 : Set.InjOn pi2 S := by
      intro X hX Y hY h
      calc X = prodSet (pi1 X) (pi2 X) := ((hrec X hX).1).symm
        _ = prodSet (pi1 Y) (pi2 Y) := by rw [hconst X hX, hconst Y hY, h]
        _ = Y := (hrec Y hY).1
    refine hf2 (pi2 '' S) ?_ ?_ ⟨pi2 C, ?_⟩
    · rintro B ⟨X, hX, rfl⟩
      exact (hrec X hX).2.2
    · rw [hinj2.ncard_image, hScard]
    · rintro A ⟨X, hX, rfl⟩ B ⟨Y, hY, rfl⟩ hAB
      have hXY : X ≠ Y := by rintro rfl; exact hAB rfl
      exact hker2 X hX Y hY hXY

/-! ### The lower-bound multiplier -/

/-- **Sunflower-free lower bounds multiply.** -/
theorem prod_lower {n₁ n₂ k M₁ M₂ : ℕ} (hk : 2 ≤ k) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (F₁ : Set (Set α)) (F₂ : Set (Set β))
    (h1 : ∀ A ∈ F₁, A.ncard = n₁) (h2 : ∀ B ∈ F₂, B.ncard = n₂)
    (hM₁ : M₁ ≤ F₁.ncard) (hM₂ : M₂ ≤ F₂.ncard)
    (hf1 : ∀ S ⊆ F₁, S.ncard = k → ¬ IsSunflower S)
    (hf2 : ∀ S ⊆ F₂, S.ncard = k → ¬ IsSunflower S) :
    M₁ * M₂ < f (n₁ + n₂) k := by
  refine lower_of_witness (α := α ⊕ β) (n₁ + n₂) k (M₁ * M₂) (by omega)
    (prodFam F₁ F₂) (prodFam_uniform hn₁ hn₂ h1 h2) ?_
    (prodFam_free hk hn₁ h1 h2 hf1 hf2)
  rw [prodFam_ncard]
  exact Nat.mul_le_mul hM₁ hM₂

end Erdos20Prod

#print axioms Erdos20Prod.prodFam_free
#print axioms Erdos20Prod.prod_lower
