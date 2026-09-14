import Mathlib
set_option autoImplicit false

def Deficient {ι α : Type*} [DecidableEq α] (t : ι → Finset α)
    (S : Finset ι) : Prop := (S.biUnion t).card < S.card

theorem hall_deficiency_blocks {ι α : Type*} [DecidableEq α]
    (t : ι → Finset α) (S : Finset ι) (hdef : Deficient t S) :
    ¬ (∃ f : ι → α, Set.InjOn f (S : Set ι)
        ∧ (∀ i, i ∈ S → f i ∈ t i)) := by
  rintro ⟨f, hinj, hmem⟩
  have hsub : S.image f ⊆ S.biUnion t := by
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact Finset.mem_biUnion.mpr ⟨i, hi, hmem i hi⟩
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact absurd hle (Nat.not_le.mpr hdef)

def divNbhd (n L k : Nat) : Finset Nat := (Finset.Ioo n (n + L)).filter (fun v => k ∣ v)

theorem e710_infeasible (n L : Nat) (S : Finset Nat)
    (hdef : Deficient (divNbhd n L) S) :
    ¬ (∃ a : Nat → Nat, Set.InjOn a (S : Set Nat)
        ∧ (∀ k, k ∈ S → a k ∈ divNbhd n L k)) :=
  hall_deficiency_blocks (divNbhd n L) S hdef

theorem e710_lower_bound_50 :
    ¬ (∃ a : Nat → Nat, Set.InjOn a (({12,20,24,30,36,40,42,45,48,50} : Finset Nat) : Set Nat)
        ∧ (∀ k, k ∈ ({12,20,24,30,36,40,42,45,48,50} : Finset Nat) → a k ∈ divNbhd 50 75 k)) := by
  apply e710_infeasible
  unfold Deficient divNbhd
  decide

theorem e710_lower_bound_100 :
    ¬ (∃ a : Nat → Nat, Set.InjOn a (({20,24,27,30,36,40,42,44,45,48,54,60,63,66,70,72,75,80,81,84,88,90,96,99,100} : Finset Nat) : Set Nat)
        ∧ (∀ k, k ∈ ({20,24,27,30,36,40,42,44,45,48,54,60,63,66,70,72,75,80,81,84,88,90,96,99,100} : Finset Nat) → a k ∈ divNbhd 100 159 k)) := by
  apply e710_infeasible
  unfold Deficient divNbhd
  decide

theorem e710_lower_bound_125 :
    ¬ (∃ a : Nat → Nat, Set.InjOn a (({30,36,40,48,50,56,60,72,80,84,90,96,100,105,108,112,120,125} : Finset Nat) : Set Nat)
        ∧ (∀ k, k ∈ ({30,36,40,48,50,56,60,72,80,84,90,96,100,105,108,112,120,125} : Finset Nat) → a k ∈ divNbhd 125 189 k)) := by
  apply e710_infeasible
  unfold Deficient divNbhd
  decide

