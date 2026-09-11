/-
Erdős Problem 20 — the Sunflower Conjecture (erdosproblems.com/20, $1000).

ATTACK 01: the Erdős–Rado sunflower lemma, kernel-checked.

The corpus file FormalConjectures/ErdosProblems/20.lean leaves
`erdos_20.variants.erdos_rado_bound` as `sorry`, and Mathlib (v4.31.0-rc1)
contains NO sunflower material whatsoever (`grep -ri sunflower Mathlib/` is empty).
This file supplies the mathematical core: any n-uniform family with more than
(k-1)^n * n! members contains a k-sunflower.

Self-contained: `import Mathlib` only.
-/
import Mathlib

set_option maxHeartbeats 1000000

namespace Erdos20Attack

open Finset

variable {α : Type*} [DecidableEq α]

/-- `S` is a sunflower with kernel `C`: any two distinct members meet exactly in `C`. -/
def SunflowerWithKernel (S : Finset (Finset α)) (C : Finset α) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = C

/-- `S` is a sunflower: some kernel works. -/
def IsSunflowerF (S : Finset (Finset α)) : Prop := ∃ C, SunflowerWithKernel S C

theorem sunflower_of_subset {S T : Finset (Finset α)} {C : Finset α}
    (h : S ⊆ T) (hT : SunflowerWithKernel T C) : SunflowerWithKernel S C :=
  fun A hA B hB hAB => hT A (h hA) B (h hB) hAB

/--
**Erdős–Rado sunflower lemma.**
Every family of `n`-element sets with more than `(k-1)^n * n!` members contains a
`k`-sunflower.
-/
theorem sunflower_lemma (k : ℕ) :
    ∀ (n : ℕ) (F : Finset (Finset α)),
      (∀ A ∈ F, A.card = n) → (k - 1) ^ n * n.factorial < F.card →
      ∃ S ⊆ F, S.card = k ∧ IsSunflowerF S := by
  intro n
  induction n with
  | zero =>
      intro F hn hcard
      exfalso
      have hsub : F ⊆ {∅} := by
        intro A hA
        have hA0 : A = ∅ := Finset.card_eq_zero.mp (hn A hA)
        simp [hA0]
      have h1 : F.card ≤ 1 := by
        have := Finset.card_le_card hsub
        simpa using this
      simp [Nat.factorial] at hcard
      omega
  | succ n ih =>
      intro F hn hcard
      classical
      -- `P` = the pairwise-disjoint subfamilies of `F`
      set P : Finset (Finset (Finset α)) :=
        F.powerset.filter (fun D => SunflowerWithKernel D (∅ : Finset α)) with hPdef
      have hPne : P.Nonempty := by
        refine ⟨∅, ?_⟩
        rw [hPdef]
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩
        intro A hA B _ _
        simp at hA
      obtain ⟨D, hDP, hDmax⟩ := Finset.exists_max_image P Finset.card hPne
      have hDF : D ⊆ F := by
        have := Finset.mem_filter.mp (hPdef ▸ hDP)
        exact Finset.mem_powerset.mp this.1
      have hDdisj : SunflowerWithKernel D (∅ : Finset α) := by
        have := Finset.mem_filter.mp (hPdef ▸ hDP)
        exact this.2
      by_cases hbig : k ≤ D.card
      · -- a big pairwise-disjoint subfamily is already a sunflower with empty kernel
        obtain ⟨S, hSD, hScard⟩ := Finset.exists_subset_card_eq hbig
        exact ⟨S, hSD.trans hDF, hScard, ⟨∅, sunflower_of_subset hSD hDdisj⟩⟩
      · push_neg at hbig
        set Y : Finset α := D.biUnion id with hYdef
        have hmemY : ∀ C ∈ D, ∀ x ∈ C, x ∈ Y := by
          intro C hC x hx
          rw [hYdef]
          exact Finset.mem_biUnion.mpr ⟨C, hC, hx⟩
        have hYcard : Y.card ≤ (k - 1) * (n + 1) := by
          have h1 : Y.card ≤ ∑ A ∈ D, (id A).card := by
            exact Finset.card_biUnion_le
          have h2 : ∑ A ∈ D, (id A).card = D.card * (n + 1) := by
            have hcongr : ∀ A ∈ D, (id A).card = n + 1 := fun A hA => hn A (hDF hA)
            rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]
          have h3 : D.card ≤ k - 1 := by omega
          calc Y.card ≤ D.card * (n + 1) := h2 ▸ h1
            _ ≤ (k - 1) * (n + 1) := Nat.mul_le_mul_right _ h3
        -- by maximality of `D`, every member of `F` meets `Y`
        have hmeet : ∀ A ∈ F, ∃ x, x ∈ A ∧ x ∈ Y := by
          intro A hA
          by_contra hcon
          push_neg at hcon
          have hAne : A.Nonempty := by
            rw [← Finset.card_pos, hn A hA]; omega
          have hAnotD : A ∉ D := by
            intro hAD
            obtain ⟨x, hx⟩ := hAne
            exact hcon x hx (hmemY A hAD x hx)
          have hdisjA : ∀ C ∈ D, A ∩ C = ∅ := by
            intro C hC
            by_contra hne
            obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
            rw [Finset.mem_inter] at hx
            exact hcon x hx.1 (hmemY C hC x hx.2)
          have hins : insert A D ∈ P := by
            rw [hPdef]
            refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
            · intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hx'
              · exact hA
              · exact hDF hx'
            · intro B hB C hC hBC
              rcases Finset.mem_insert.mp hB with rfl | hB'
              · rcases Finset.mem_insert.mp hC with rfl | hC'
                · exact absurd rfl hBC
                · exact hdisjA C hC'
              · rcases Finset.mem_insert.mp hC with rfl | hC'
                · rw [Finset.inter_comm]; exact hdisjA B hB'
                · exact hDdisj B hB' C hC' hBC
          have hlt : D.card < (insert A D).card :=
            Finset.card_lt_card (Finset.ssubset_insert hAnotD)
          have := hDmax _ hins
          omega
        -- pigeonhole on `Y`
        have hex : ∃ y ∈ Y, (k - 1) ^ n * n.factorial <
            (F.filter (fun A => y ∈ A)).card := by
          by_contra hcon
          push_neg at hcon
          have hcover : F ⊆ Y.biUnion (fun y => F.filter (fun A => y ∈ A)) := by
            intro A hA
            obtain ⟨x, hxA, hxY⟩ := hmeet A hA
            exact Finset.mem_biUnion.mpr ⟨x, hxY, Finset.mem_filter.mpr ⟨hA, hxA⟩⟩
          have hle : F.card ≤ (k - 1) ^ (n + 1) * (n + 1).factorial := by
            calc F.card ≤ (Y.biUnion (fun y => F.filter (fun A => y ∈ A))).card :=
                  Finset.card_le_card hcover
              _ ≤ ∑ y ∈ Y, (F.filter (fun A => y ∈ A)).card := Finset.card_biUnion_le
              _ ≤ ∑ _y ∈ Y, (k - 1) ^ n * n.factorial := Finset.sum_le_sum hcon
              _ = Y.card * ((k - 1) ^ n * n.factorial) := by
                  simp [Finset.sum_const, smul_eq_mul]
              _ ≤ ((k - 1) * (n + 1)) * ((k - 1) ^ n * n.factorial) :=
                  Nat.mul_le_mul_right _ hYcard
              _ = (k - 1) ^ (n + 1) * (n + 1).factorial := by
                  rw [pow_succ, Nat.factorial_succ]; ring
          omega
        obtain ⟨y, _hyY, hy⟩ := hex
        set G : Finset (Finset α) := F.filter (fun A => y ∈ A) with hGdef
        have hGF : G ⊆ F := by rw [hGdef]; exact Finset.filter_subset _ _
        have hyG : ∀ A ∈ G, y ∈ A := by
          intro A hA
          have := Finset.mem_filter.mp (hGdef ▸ hA)
          exact this.2
        set F' : Finset (Finset α) := G.image (fun A => A.erase y) with hF'def
        have hinj : Set.InjOn (fun A => A.erase y) (↑G : Set (Finset α)) := by
          intro A hA B hB hAB
          simp only at hAB
          have eA := Finset.insert_erase (hyG A (Finset.mem_coe.mp hA))
          have eB := Finset.insert_erase (hyG B (Finset.mem_coe.mp hB))
          rw [← eA, ← eB, hAB]
        have hF'card : (k - 1) ^ n * n.factorial < F'.card := by
          rw [hF'def, Finset.card_image_of_injOn hinj]
          exact hy
        have hF'n : ∀ B ∈ F', B.card = n := by
          intro B hB
          obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp (hF'def ▸ hB)
          rw [Finset.card_erase_of_mem (hyG A hA), hn A (hGF hA)]
          omega
        obtain ⟨S', hS'F', hS'card, C, hC⟩ := ih F' hF'n hF'card
        have hynotB : ∀ B ∈ F', y ∉ B := by
          intro B hB
          obtain ⟨A, _hA, rfl⟩ := Finset.mem_image.mp (hF'def ▸ hB)
          intro hcon
          exact (Finset.mem_erase.mp hcon).1 rfl
        refine ⟨S'.image (insert y), ?_, ?_, ⟨insert y C, ?_⟩⟩
        · intro T hT
          obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hT
          obtain ⟨A, hA, hAB⟩ := Finset.mem_image.mp (hF'def ▸ hS'F' hB)
          rw [← hAB, Finset.insert_erase (hyG A hA)]
          exact hGF hA
        · rw [Finset.card_image_of_injOn, hS'card]
          intro B₁ h1 B₂ h2 h12
          have e1 := Finset.erase_insert (hynotB B₁ (hS'F' (Finset.mem_coe.mp h1)))
          have e2 := Finset.erase_insert (hynotB B₂ (hS'F' (Finset.mem_coe.mp h2)))
          rw [← e1, ← e2, h12]
        · intro T₁ hT₁ T₂ hT₂ hne
          obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_image.mp hT₁
          obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_image.mp hT₂
          have hB : B₁ ≠ B₂ := by rintro rfl; exact hne rfl
          have hker := hC B₁ hB₁ B₂ hB₂ hB
          ext x
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨h1, h2⟩
            rcases h1 with rfl | h1
            · exact Or.inl rfl
            · rcases h2 with rfl | h2
              · exact Or.inl rfl
              · exact Or.inr (hker ▸ Finset.mem_inter.mpr ⟨h1, h2⟩)
          · rintro (rfl | h)
            · exact ⟨Or.inl rfl, Or.inl rfl⟩
            · rw [← hker, Finset.mem_inter] at h
              exact ⟨Or.inr h.1, Or.inr h.2⟩

end Erdos20Attack
