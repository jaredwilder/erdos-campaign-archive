import Mathlib

set_option autoImplicit false



namespace Erdos241Closer

/-- The frozen B₃ predicate (the multiset condition inside the contract's `f`). -/
def IsB3 (A : Finset ℕ) : Prop :=
  ∀ m₁ m₂ : Multiset ℕ, m₁.card = 3 → m₂.card = 3 →
    (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) → m₁.sum = m₂.sum → m₁ = m₂

/-- The 3-fold multiset of an ordered triple. -/
def tripleMs (p : ℕ × ℕ × ℕ) : Multiset ℕ := (([p.1, p.2.1, p.2.2] : List ℕ) : Multiset ℕ)

end Erdos241Closer

theorem msl_fmz_erdos241_campaign_001_R004_L1  : theorem Erdos241Closer.counting_bound (N : ℕ) (A : Finset ℕ)
    (hA : ∀ x ∈ A, 1 ≤ x ∧ x ≤ N) (hB3 : Erdos241Closer.IsB3 A) :
    A.card ^ 3 ≤ 27 * (3 * N + 1) := by
  classical
  set S : Finset (ℕ × ℕ × ℕ) := A ×ˢ (A ×ˢ A) with hSdef
  have hScard : S.card = A.card ^ 3 := by
    simp only [hSdef, Finset.card_product]; ring
  have hmemA : ∀ p ∈ S, ∀ x ∈ tripleMs p, x ∈ A := by
    intro p hp x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    obtain ⟨h3, h4⟩ := Finset.mem_product.1 h2
    have hx' : x ∈ ([p.1, p.2.1, p.2.2] : List ℕ) := Multiset.mem_coe.1 hx
    simp only [List.mem_cons, List.mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl
    · exact h1
    · exact h3
    · exact h4
  have hB3app : ∀ p q ∈ S, p.1 + p.2.1 + p.2.2 = q.1 + q.2.1 + q.2.2 →
      tripleMs p = tripleMs q := by
    intro p hp q hq hs
    exact hB3 (tripleMs p) (tripleMs q) (by simp [tripleMs]) (by simp [tripleMs])
      (hmemA p hp) (hmemA q hq) (by simpa [tripleMs] using hs)
  have hcoord : ∀ p q ∈ S, tripleMs p = tripleMs q →
      p.1 ∈ ({q.1, q.2.1, q.2.2} : Finset ℕ) ∧
      p.2.1 ∈ ({q.1, q.2.1, q.2.2} : Finset ℕ) ∧
      p.2.2 ∈ ({q.1, q.2.1, q.2.2} : Finset ℕ) := by
    intro p hp q hq heq
    have hmem : ∀ x ∈ tripleMs p, x ∈ ({q.1, q.2.1, q.2.2} : Finset ℕ) := by
      intro x hx
      rw [heq] at hx
      simpa [tripleMs] using hx
    exact ⟨hmem p.1 (by simp [tripleMs]), hmem p.2.1 (by simp [tripleMs]),
      hmem p.2.2 (by simp [tripleMs])⟩
  have hfiber : ∀ b : ℕ,
      (S.filter (fun p => p.1 + p.2.1 + p.2.2 = b)).card ≤ 27 := by
    intro b
    by_cases hex : ∃ p₀, p₀ ∈ S.filter (fun p => p.1 + p.2.1 + p.2.2 = b)
    · obtain ⟨p₀, hp₀⟩ := hex
      have hp₀S : p₀ ∈ S := (Finset.mem_filter.1 hp₀).1
      have hsum₀ : p₀.1 + p₀.2.1 + p₀.2.2 = b := (Finset.mem_filter.1 hp₀).2
      have heq : tripleMs p = tripleMs p₀ :=
        hB3app p hpS_aux p₀ hp₀S
          ((Finset.mem_filter.1 (p ∈ S.filter (fun p => p.1 + p.2.1 + p.2.2 = b) → p ∈ S.filter (fun p => p.1 + p.2.1 + p.2.2 = b))).2.trans hsum₀.symm)
      · have hsub : S.filter (fun p => p.1 + p.2.1 + p.2.2 = b) ⊆
          (({p₀.1, p₀.2.1, p₀.2.2} : Finset ℕ) ×ˢ
           (({p₀.1, p₀.2.1, p₀.2.2} : Finset ℕ) ×ˢ
            ({p₀.1, p₀.2.1, p₀.2.2} : Finset ℕ))) := by
          intro p hp
          have hpS : p ∈ S := (Finset.mem_filter.1 hp).1
          obtain ⟨h1, h2, h3⟩ := hcoord p hpS p₀ hp₀S heq
          exact Finset.mem_product.2 ⟨h1, Finset.mem_product.2 ⟨h2, h3⟩⟩
        have hc3 : ({p₀.1, p₀.2.1, p₀.2.2} : Finset ℕ).card ≤ 3 := by
          refine le_trans (Finset.card_insert_le _ _) ?_
          refine le_trans (Finset.card_insert_le _ _) ?_
          simp
        have key : ∀ n : ℕ, n ≤ 3 → n * (n * n) ≤ 27 := by
          intro n hn
          rcases Nat.eq_or_lt_of_le hn with rfl | h
          · norm_num
          · have h2 : n ≤ 2 := by omega
            rcases Nat.eq_or_lt_of_le h2 with rfl | h
            · norm_num
            · have h1 : n ≤ 1 := by omega
              rcases Nat.eq_or_lt_of_le h1 with rfl | h
              · norm_num
              · have h0 : n = 0 := Nat.le_zero.mp (by omega)
                subst h0
                norm_num
        refine le_trans (Finset.card_le_card hsub) ?_
        rw [Finset.card_product, Finset.card_product]
        exact key _ hc3
    · have hempty : (S.filter (fun p => p.1 + p.2.1 + p.2.2 = b)) = ∅ :=
        Finset.eq_empty_iff_forall_notMem.2 (fun p hp => hex ⟨p, hp⟩)
      simp [hempty]

-- axiom footprint
#print axioms Erdos241Closer.IsB3
#print axioms Erdos241Closer.tripleMs
#print axioms msl_fmz_erdos241_campaign_001_R004_L1
