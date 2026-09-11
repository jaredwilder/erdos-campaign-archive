import Mathlib

set_option autoImplicit false

namespace Erdos595Star

variable {V : Type*}

def star (G : SimpleGraph V) (v : V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => x = v ∧ G.Adj x y)

theorem star_adj_endpoint (G : SimpleGraph V) (v : V) :
    ∀ x y : V, (star G v).Adj x y → x = v ∨ y = v := by
  intro x y h
  simp only [star, SimpleGraph.fromRel_adj] at h
  rcases h with ⟨-, ⟨hx, -⟩ | ⟨hy, -⟩⟩
  · exact Or.inl hx
  · exact Or.inr hy

theorem star_le (G : SimpleGraph V) (v : V) : star G v ≤ G := by
  intro x y h
  simp only [star, SimpleGraph.fromRel_adj] at h
  rcases h with ⟨-, ⟨-, ha⟩ | ⟨-, ha⟩⟩
  · exact ha
  · exact ha.symm

theorem star_cliqueFree (G : SimpleGraph V) (v : V) : (star G v).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hs.2
  subst hset
  have key := star_adj_endpoint G v
  by_cases hav : a = v
  · have h1 := key b c (hs.1 (by simp) (by simp) hbc)
    rcases h1 with hbv | hcv
    · exact hab (hav.trans hbv.symm)
    · exact hac (hav.trans hcv.symm)
  · by_cases hbv : b = v
    · have h1 := key a c (hs.1 (by simp) (by simp) hac)
      rcases h1 with h | h
      · exact hav h
      · exact hbc (hbv.trans h.symm)
    · have h1 := key a b (hs.1 (by simp) (by simp) hab)
      rcases h1 with h | h
      · exact hav h
      · exact hbv h

theorem star_edgeSet_uncountable (G : SimpleGraph V) (v : V)
    (h : ¬ (G.neighborSet v).Countable) : ¬ (star G v).edgeSet.Countable := by
  intro hc
  apply h
  have hinj : Function.Injective (fun u : V => s(v, u)) := fun u u' he => Sym2.congr_right.mp he
  have hpre : G.neighborSet v ⊆ (fun u : V => s(v, u)) ⁻¹' (star G v).edgeSet := by
    intro u hu
    have hadj : G.Adj v u := hu
    have hne : v ≠ u := G.ne_of_adj hadj
    apply (star G v).mem_edgeSet.mpr
    show (SimpleGraph.fromRel fun x y => x = v ∧ G.Adj x y).Adj v u
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl ⟨rfl, hadj⟩⟩
  exact ((hc.preimage hinj).mono hpre)

end Erdos595Star

theorem msl_erdos595_star_k219s_v4_2026_09_05 {V : Type*} (G : SimpleGraph V) (v : V) (h : ¬ (G.neighborSet v).Countable) : ∃ H : SimpleGraph V, H ≤ G ∧ H.CliqueFree 3 ∧ ¬ H.edgeSet.Countable := by exact ⟨Erdos595Star.star G v, Erdos595Star.star_le G v, Erdos595Star.star_cliqueFree G v, Erdos595Star.star_edgeSet_uncountable G v h⟩
