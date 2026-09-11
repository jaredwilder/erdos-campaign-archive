/- Probe v2: the 5-cycle witness for R(3,3) > 5, without any CliqueFree decidability. -/
import Mathlib

/-- The 5-cycle on `Fin 5` (arithmetic mod 5). -/
def C5 : SimpleGraph (Fin 5) where
  Adj a b := a + 1 = b ∨ b + 1 = a
  symm := by
    intro a b h
    exact h.symm
  loopless := ⟨by decide⟩

instance : DecidableRel C5.Adj := fun a b =>
  inferInstanceAs (Decidable (a + 1 = b ∨ b + 1 = a))

instance : DecidableRel C5ᶜ.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ¬ C5.Adj a b))

theorem C5_triangleFree : C5.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.2
  have h1 : C5.Adj a b := ht.1 (by simp) (by simp) hab
  have h2 : C5.Adj a c := ht.1 (by simp) (by simp) hac
  have h3 : C5.Adj b c := ht.1 (by simp) (by simp) hbc
  revert hab hac hbc h1 h2 h3
  revert a b c
  decide

theorem C5_compl_cliqueFree_three : C5ᶜ.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.2
  have h1 : C5ᶜ.Adj a b := ht.1 (by simp) (by simp) hab
  have h2 : C5ᶜ.Adj a c := ht.1 (by simp) (by simp) hac
  have h3 : C5ᶜ.Adj b c := ht.1 (by simp) (by simp) hbc
  revert hab hac hbc h1 h2 h3
  revert a b c
  decide

#print axioms C5_triangleFree
#print axioms C5_compl_cliqueFree_three
