import Mathlib
open Filter Topology Finset

-- Probe 03: name-drift reconnaissance for Attack02 (Shearer). `#check` only, proves nothing.

#check @Finset.exists_subset_card_eq
#check @Finset.card_union_le
#check @Finset.card_insert_le
#check @Finset.card_erase_of_mem
#check @Finset.card_fin
#check @Finset.card_eq_three
#check @Finset.mem_erase
#check @Finset.card_union_of_disjoint
#check @Finset.disjoint_left
#check @Nat.mul_le_mul
#check @mul_lt_mul_of_pos_left
#check @Real.log_lt_sub_one_of_pos
#check @Real.log_pos
#check @Real.exp_lt_exp
#check @Real.log_lt_log
#check @Real.log_exp
#check @lt_div_iff₀
#check @div_lt_iff₀
#check @SimpleGraph.compl_adj
#check @SimpleGraph.Adj.ne'
#check @SimpleGraph.cliqueFree_bot
#check @SimpleGraph.cliqueFree_of_card_lt
#check @compl_compl

-- shape probes
example (V : Type) [DecidableEq V] (s : Finset V) (k : ℕ) (h : k ≤ s.card) :
    ∃ u ⊆ s, u.card = k := Finset.exists_subset_card_eq h

example (x : ℝ) (hx : 0 < x) (hx1 : 1 < x) : Real.log x < x - 1 :=
  Real.log_lt_sub_one_of_pos hx hx1.ne'

example (a b c : ℝ) (hc : 0 < c) : a < b / c ↔ a * c < b := lt_div_iff₀ hc

example (a b c : ℝ) (hc : 0 < c) : a / c < b ↔ a < b * c := div_lt_iff₀ hc

example (V : Type) [DecidableEq V] (s t : Finset V) (h : Disjoint s t) :
    (s ∪ t).card = s.card + t.card := Finset.card_union_of_disjoint h

example (n : ℕ) : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n

example (V : Type) [DecidableEq V] (G : SimpleGraph V) (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : ({a, b, c} : Finset V).card = 3 :=
  Finset.card_eq_three.mpr ⟨a, b, c, hab.ne, hac.ne, hbc.ne, rfl⟩

-- classical neighbourhood-cover construction used everywhere in Attack02
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ N : Fin n → Finset (Fin n), ∀ v w, w ∈ N v ↔ G.Adj v w := by
  classical
  exact ⟨fun v => Finset.univ.filter (fun w => G.Adj v w), by intro v w; simp⟩
