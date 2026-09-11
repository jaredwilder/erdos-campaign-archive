import Mathlib
open Filter Finset

#check @Set.ncard_eq_toFinset_card
#check @Set.Finite.card_toFinset
#check @Set.toFinset_card
#check @Set.ncard_eq_toFinset_card'

def countSet (A : Set ℕ) (x : ℝ) : Set ℕ := {n | n ∈ A ∧ 1 ≤ n ∧ (n : ℝ) ≤ x}

example (A : Set ℕ) (x : ℝ) (hfin : (countSet A x).Finite) :
    (countSet A x).ncard = hfin.toFinset.card := by
  exact?
