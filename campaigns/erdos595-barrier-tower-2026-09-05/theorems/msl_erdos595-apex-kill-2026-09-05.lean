import Mathlib

set_option autoImplicit false

namespace Erdos595Apex

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
  have hxyne : x ≠ y := hxy.ne
  have hyzne : y ≠ z := hyz.ne
  have hxzne : x ≠ z := hxz.ne
  rcases key x y hxy with hx | hy
  · rcases key y z hyz with hy' | hz'
    · exact hxyne (hx.trans hy'.symm)
    · exact hxzne (hx.trans hz'.symm)
  · rcases key x z hxz with hx' | hz'
    · exact hxyne (hx'.trans hy.symm)
    · exact hyzne (hy.trans hz'.symm)

theorem star_mem_edgeSet (G : SimpleGraph V) (v y : V) (h : G.Adj v y) :
    s(v, y) ∈ (star G v).edgeSet := by
  apply (star G v).mem_edgeSet.mpr
  show (SimpleGraph.fromRel fun a b => a = v ∧ G.Adj a b).Adj v y
  rw [SimpleGraph.fromRel_adj]
  exact ⟨G.ne_of_adj h, Or.inl ⟨rfl, h⟩⟩

theorem coverable_of_countable_hitting_set (G : SimpleGraph V) (S : Set V)
    (hS : S.Countable)
    (hhit : ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z → x ∈ S ∨ y ∈ S ∨ z ∈ S) :
    Coverable G := by
  classical
  set G0 : SimpleGraph V := SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → x ∉ S}
    with hG0
  have hG0le : G0 ≤ G := by
    intro x y h
    rw [hG0, SimpleGraph.fromEdgeSet_adj] at h
    exact G.mem_edgeSet.mp h.1.1
  have hG0free : G0.CliqueFree 3 := by
    rw [cliqueFree_three_iff]
    intro x y z hxy hyz hxz
    have hxy' := hxy
    have hyz' := hyz
    have hxz' := hxz
    rw [hG0, SimpleGraph.fromEdgeSet_adj] at hxy' hyz' hxz'
    have hxS : x ∉ S := hxy'.1.2 x (by simp)
    have hyS : y ∉ S := hxy'.1.2 y (by simp)
    have hzS : z ∉ S := hyz'.1.2 z (by simp)
    rcases hhit x y z (hG0le hxy) (hG0le hyz) (hG0le hxz) with h | h | h
    · exact hxS h
    · exact hyS h
    · exact hzS h
  rcases Set.eq_empty_or_nonempty S with hemp | hne
  · refine ⟨fun _ => G0, fun n => hG0le, fun n => hG0free, ?_⟩
    intro e he
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    rw [hG0, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨⟨he, ?_⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩
    intro x _
    rw [hemp]
    exact Set.notMem_empty x
  · obtain ⟨f, hf⟩ := hS.exists_eq_range hne
    refine ⟨fun n => Nat.rec G0 (fun m _ => star G (f m)) n, ?_, ?_, ?_⟩
    · intro n
      cases n with
      | zero => exact hG0le
      | succ m => exact star_le G (f m)
    · intro n
      cases n with
      | zero => exact hG0free
      | succ m => exact star_cliqueFree G (f m)
    · intro e he
      induction e using Sym2.ind with
      | _ x y =>
        have hadj : G.Adj x y := G.mem_edgeSet.mp he
        by_cases hxS : x ∈ S
        · obtain ⟨n, hn⟩ : ∃ n, f n = x := by
            have : x ∈ Set.range f := by rw [← hf]; exact hxS
            exact this
          refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
          show s(x, y) ∈ (star G (f n)).edgeSet
          rw [hn]
          exact star_mem_edgeSet G x y hadj
        · by_cases hyS : y ∈ S
          · obtain ⟨n, hn⟩ : ∃ n, f n = y := by
              have : y ∈ Set.range f := by rw [← hf]; exact hyS
              exact this
            refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
            show s(x, y) ∈ (star G (f n)).edgeSet
            rw [hn, Sym2.eq_swap]
            exact star_mem_edgeSet G y x hadj.symm
          · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
            show s(x, y) ∈ G0.edgeSet
            rw [hG0, SimpleGraph.edgeSet_fromEdgeSet]
            refine ⟨⟨he, ?_⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩
            intro w hw
            rcases Sym2.mem_iff.mp hw with rfl | rfl
            · exact hxS
            · exact hyS

end Erdos595Apex

theorem msl_erdos595_apex_kill_2026_09_05 {V : Type*} (G : SimpleGraph V) (S : Set V) (hS : S.Countable) (hhit : ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z → x ∈ S ∨ y ∈ S ∨ z ∈ S) : Erdos595Apex.Coverable G := by exact Erdos595Apex.coverable_of_countable_hitting_set G S hS hhit
