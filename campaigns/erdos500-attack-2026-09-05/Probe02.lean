/- Second reconnaissance pass: names needed for the 5-set averaging bound. -/
import Mathlib

#check @Finset.union_sdiff_of_subset
#check @Finset.union_sdiff_cancel_left
#check @Finset.sdiff_subset_sdiff
#check @Finset.card_sdiff_add_card_eq_card
#check @Finset.subset_union_left
#check @Finset.disjoint_right
#check @Finset.card_pos
#check @Finset.card_sdiff
#check @Nat.eq_of_mul_eq_mul_right
#check @Nat.choose_one_right
#check @Finset.Subset.refl

-- does `ring` cope with ℕ truncated subtraction as an atom?
example (n a b : ℕ) : (a * (n - 3)) * b = a * ((n - 3) * b) := by ring
example (n a : ℕ) : (a * ((n - 3).choose 2)) * 2 = a * ((n - 3).choose 2 * 2) := by ring
