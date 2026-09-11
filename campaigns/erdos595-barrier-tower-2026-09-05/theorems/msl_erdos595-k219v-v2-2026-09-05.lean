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

namespace Erdos595Match

variable {V : Type*}

theorem fromEdgeSet_le_of_subset (G : SimpleGraph V) {M : Set (Sym2 V)}
    (hsub : M ⊆ G.edgeSet) : SimpleGraph.fromEdgeSet M ≤ G := by
  intro x y h
  rw [SimpleGraph.fromEdgeSet_adj] at h
  exact G.mem_edgeSet.mp (hsub h.1)

theorem matching_cliqueFree {M : Set (Sym2 V)}
    (hM : M.Pairwise fun e f => ∀ x, x ∈ e → x ∉ f) :
    (SimpleGraph.fromEdgeSet M).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hs.2
  subst hset
  have h1 : (SimpleGraph.fromEdgeSet M).Adj a b := hs.1 (by simp) (by simp) hab
  have h2 : (SimpleGraph.fromEdgeSet M).Adj b c := hs.1 (by simp) (by simp) hbc
  rw [SimpleGraph.fromEdgeSet_adj] at h1 h2
  by_cases heq : s(a, b) = s(b, c)
  · rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h3, -⟩ | ⟨h3, -⟩
    · exact hab h3
    · exact hac h3
  · exact (hM h1.1 h2.1 heq) b (by simp [Sym2.mem_iff]) (by simp [Sym2.mem_iff])

theorem uncountable_triangleFree_subgraph (G : SimpleGraph V)
    (h : ¬ G.edgeSet.Countable) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.CliqueFree 3 ∧ ¬ H.edgeSet.Countable := by
  classical
  by_cases hdeg : ∀ v : V, (G.neighborSet v).Countable
  · set S : Set (Set (Sym2 V)) :=
      {M | M ⊆ G.edgeSet ∧ M.Pairwise fun e f => ∀ x, x ∈ e → x ∉ f} with hSdef
    have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ t ∈ c, t ⊆ ub := by
      intro c hcS hch
      refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun t ht => Set.subset_sUnion_of_mem ht⟩
      · intro e he
        obtain ⟨t, htc, het⟩ := he
        exact (hcS htc).1 het
      · intro e he f hf hef
        obtain ⟨t, htc, het⟩ := he
        obtain ⟨u, huc, hfu⟩ := hf
        rcases hch.total htc huc with hle | hle
        · exact (hcS huc).2 (hle het) hfu hef
        · exact (hcS htc).2 het (hle hfu) hef
    obtain ⟨M, hM⟩ := zorn_subset S hchain
    have hMsub : M ⊆ G.edgeSet := hM.1.1
    have hMpw : M.Pairwise fun e f => ∀ x, x ∈ e → x ∉ f := hM.1.2
    have hmeet : ∀ e ∈ G.edgeSet, ∃ f ∈ M, ∃ x, x ∈ e ∧ x ∈ f := by
      intro e he
      by_cases heM : e ∈ M
      · obtain ⟨a, ha⟩ : ∃ a, a ∈ e := by
          induction e using Sym2.ind with
          | _ a b => exact ⟨a, by simp [Sym2.mem_iff]⟩
        exact ⟨e, heM, a, ha, ha⟩
      · have hins : insert e M ∉ S := by
          intro hmem
          exact heM (hM.2 hmem (Set.subset_insert e M) (Set.mem_insert e M))
        have hpair : ¬ (insert e M).Pairwise fun e f => ∀ x, x ∈ e → x ∉ f := by
          intro hp
          exact hins ⟨Set.insert_subset he hMsub, hp⟩
        obtain ⟨f, hfM, hef, hbad⟩ :
            ∃ f ∈ M, e ≠ f ∧
              ¬((∀ x, x ∈ e → x ∉ f) ∧ (∀ x, x ∈ f → x ∉ e)) := by
          by_contra hcon
          push_neg at hcon
          exact hpair (Set.pairwise_insert.mpr ⟨hMpw, fun f hf hef => hcon f hf hef⟩)
        rcases not_and_or.mp hbad with hb | hb
        · push_neg at hb
          obtain ⟨x, hxe, hxf⟩ := hb
          exact ⟨f, hfM, x, hxe, hxf⟩
        · push_neg at hb
          obtain ⟨x, hxf, hxe⟩ := hb
          exact ⟨f, hfM, x, hxe, hxf⟩
    have hMc : ¬ M.Countable := by
      intro hMc
      apply h
      have hVM : (⋃ f ∈ M, {x | x ∈ f}).Countable := by
        refine hMc.biUnion fun f _ => ?_
        induction f using Sym2.ind with
        | _ a b =>
          have hab2 : {x | x ∈ s(a, b)} = {a, b} := by
            ext x
            simp [Sym2.mem_iff]
          rw [hab2]
          exact (Set.toFinite _).countable
      have hxcount : ∀ x : V, {e | e ∈ G.edgeSet ∧ x ∈ e}.Countable := by
        intro x
        have hsub2 : {e | e ∈ G.edgeSet ∧ x ∈ e} ⊆ (fun u => s(x, u)) '' (G.neighborSet x) := by
          rintro e ⟨he, hxe⟩
          obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
          exact ⟨y, G.mem_edgeSet.mp he, rfl⟩
        exact ((hdeg x).image _).mono hsub2
      have hcover : G.edgeSet ⊆ ⋃ x ∈ (⋃ f ∈ M, {y | y ∈ f}), {e | e ∈ G.edgeSet ∧ x ∈ e} := by
        intro e he
        obtain ⟨f, hfM, x, hxe, hxf⟩ := hmeet e he
        exact Set.mem_biUnion (Set.mem_biUnion hfM hxf) ⟨he, hxe⟩
      exact ((hVM.biUnion fun x _ => hxcount x).mono hcover)
    refine ⟨SimpleGraph.fromEdgeSet M, fromEdgeSet_le_of_subset G hMsub,
      matching_cliqueFree hMpw, ?_⟩
    have hsubM : M ⊆ (SimpleGraph.fromEdgeSet M).edgeSet := by
      intro e he
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨he, fun hd => (G.not_isDiag_of_mem_edgeSet (hMsub he)) hd⟩
    exact fun hc => hMc (hc.mono hsubM)
  · push_neg at hdeg
    obtain ⟨v, hv⟩ := hdeg
    exact ⟨Erdos595Star.star G v, Erdos595Star.star_le G v,
      Erdos595Star.star_cliqueFree G v, Erdos595Star.star_edgeSet_uncountable G v hv⟩

end Erdos595Match

theorem msl_erdos595_k219v_v2_2026_09_05 {V : Type*} (G : SimpleGraph V) (h : ¬ G.edgeSet.Countable) : ∃ H : SimpleGraph V, H ≤ G ∧ H.CliqueFree 3 ∧ ¬ H.edgeSet.Countable := by exact Erdos595Match.uncountable_triangleFree_subgraph G h
