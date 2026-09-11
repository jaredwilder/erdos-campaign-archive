import Mathlib

set_option autoImplicit false

namespace Erdos595Succ

variable {V : Type*}

def Coverable (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ n, H n ≤ G) ∧ (∀ n, (H n).CliqueFree 3) ∧
    G.edgeSet ⊆ ⋃ n, (H n).edgeSet

theorem cliqueFree_three_iff (G : SimpleGraph V) :
    G.CliqueFree 3 ↔ ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z → False := by
  classical
  constructor
  · intro hG x y z hxy hyz hxz
    exact hG {x, y, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
  · intro h s hs
    obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.mp hs.2
    subst hset
    exact h x y z (hs.1 (by simp) (by simp) hxy) (hs.1 (by simp) (by simp) hyz)
      (hs.1 (by simp) (by simp) hxz)

def star (G : SimpleGraph V) (v : V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => x = v ∧ G.Adj x y)

theorem star_le (G : SimpleGraph V) (v : V) : star G v ≤ G := by
  intro x y h
  simp only [star, SimpleGraph.fromRel_adj] at h
  rcases h with ⟨-, ⟨-, ha⟩ | ⟨-, ha⟩⟩
  · exact ha
  · exact ha.symm

theorem star_adj_endpoint (G : SimpleGraph V) (v : V) :
    ∀ x y : V, (star G v).Adj x y → x = v ∨ y = v := by
  intro x y h
  simp only [star, SimpleGraph.fromRel_adj] at h
  rcases h with ⟨-, ⟨hx, -⟩ | ⟨hy, -⟩⟩
  · exact Or.inl hx
  · exact Or.inr hy

theorem star_cliqueFree (G : SimpleGraph V) (v : V) : (star G v).CliqueFree 3 := by
  rw [cliqueFree_three_iff]
  intro x y z hxy hyz hxz
  have key := star_adj_endpoint G v
  rcases key x y hxy with hx | hy
  · rcases key y z hyz with hy' | hz'
    · exact hxy.ne (hx.trans hy'.symm)
    · exact hxz.ne (hx.trans hz'.symm)
  · rcases key x z hxz with hx' | hz'
    · exact hxy.ne (hx'.trans hy.symm)
    · exact hyz.ne (hy.trans hz'.symm)

theorem star_mem_edgeSet (G : SimpleGraph V) (v y : V) (h : G.Adj v y) :
    s(v, y) ∈ (star G v).edgeSet := by
  apply (star G v).mem_edgeSet.mpr
  show (SimpleGraph.fromRel fun a b => a = v ∧ G.Adj a b).Adj v y
  rw [SimpleGraph.fromRel_adj]
  exact ⟨G.ne_of_adj h, Or.inl ⟨rfl, h⟩⟩

theorem coverable_add_vertex (G H : SimpleGraph V) (v : V) (hGH : G ≤ H)
    (hnew : ∀ x y : V, H.Adj x y → ¬ G.Adj x y → x = v ∨ y = v)
    (hG : Coverable G) : Coverable H := by
  classical
  obtain ⟨K, hKle, hKfree, hKcov⟩ := hG
  refine ⟨fun n => Nat.rec (star H v) (fun m _ => K m) n, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact star_le H v
    | succ m => exact le_trans (hKle m) hGH
  · intro n
    cases n with
    | zero => exact star_cliqueFree H v
    | succ m => exact hKfree m
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hHadj : H.Adj x y := H.mem_edgeSet.mp he
      by_cases hGadj : G.Adj x y
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hKcov (G.mem_edgeSet.mpr hGadj))
        exact Set.mem_iUnion.mpr ⟨n + 1, hn⟩
      · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
        rcases hnew x y hHadj hGadj with rfl | rfl
        · exact star_mem_edgeSet H x y hHadj
        · rw [Sym2.eq_swap]
          exact star_mem_edgeSet H y x hHadj.symm

end Erdos595Succ

theorem msl_erdos595_successor_step_2026_09_05 {V : Type*} (G H : SimpleGraph V) (v : V) (hGH : G ≤ H) (hnew : ∀ x y : V, H.Adj x y → ¬ G.Adj x y → x = v ∨ y = v) (hG : Erdos595Succ.Coverable G) : Erdos595Succ.Coverable H := by exact Erdos595Succ.coverable_add_vertex G H v hGH hnew hG
