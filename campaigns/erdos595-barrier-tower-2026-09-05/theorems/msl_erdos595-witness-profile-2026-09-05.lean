import Mathlib

set_option autoImplicit false

namespace Erdos595CB

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

theorem colouring_cover (G : SimpleGraph V) (c : Sym2 V → ℕ)
    (hc : ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z →
      ¬ (c s(x, y) = c s(y, z) ∧ c s(x, z) = c s(y, z))) : Coverable G := by
  classical
  refine ⟨fun n => SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = n}, ?_, ?_, ?_⟩
  · intro n x y h
    rw [SimpleGraph.fromEdgeSet_adj] at h
    exact G.mem_edgeSet.mp h.1.1
  · intro n
    rw [cliqueFree_three_iff]
    intro x y z hxy hyz hxz
    rw [SimpleGraph.fromEdgeSet_adj] at hxy hyz hxz
    exact hc x y z (G.mem_edgeSet.mp hxy.1.1) (G.mem_edgeSet.mp hyz.1.1)
      (G.mem_edgeSet.mp hxz.1.1)
      ⟨hxy.1.2.trans hyz.1.2.symm, hxz.1.2.trans hyz.1.2.symm⟩
  · intro e he
    refine Set.mem_iUnion.mpr ⟨c e, ?_⟩
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨⟨he, rfl⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩

variable [LinearOrder V]

noncomputable def backCol (g : V → V → ℕ) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => if x < y then g y x else g x y, by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, asymm h]
    · simp [h]
    · simp [h, asymm h]⟩

theorem backCol_lt (g : V → V → ℕ) (a b : V) (h : a < b) :
    backCol g s(a, b) = g b a := by
  simp [backCol, Sym2.lift_mk, h]

theorem backCol_gt (g : V → V → ℕ) (a b : V) (h : b < a) :
    backCol g s(a, b) = g a b := by
  simp [backCol, Sym2.lift_mk, asymm h]

theorem coverable_of_local_colouring (G : SimpleGraph V) (g : V → V → ℕ)
    (hg : ∀ v a b : V, a < v → b < v → G.Adj a v → G.Adj b v → G.Adj a b →
      g v a ≠ g v b) : Coverable G := by
  classical
  refine colouring_cover G (backCol g) ?_
  rintro x y z hxy hyz hxz ⟨h1, h2⟩
  rcases lt_trichotomy x y with hA | hA | hA
  · rcases lt_trichotomy y z with hB | hB | hB
    · have hxz' : x < z := hA.trans hB
      rw [backCol_lt g x z hxz', backCol_lt g y z hB] at h2
      exact hg z x y hxz' hB hxz hyz hxy h2
    · exact hyz.ne hB
    · rw [backCol_lt g x y hA, backCol_gt g y z hB] at h1
      exact hg y x z hA hB hxy hyz.symm hxz h1
  · exact hxy.ne hA
  · rcases lt_trichotomy x z with hB | hB | hB
    · have hyz' : y < z := hA.trans hB
      rw [backCol_lt g x z hB, backCol_lt g y z hyz'] at h2
      exact hg z x y hB hyz' hxz hyz hxy h2
    · exact hxz.ne hB
    · rw [backCol_gt g x y hA] at h1
      rw [backCol_gt g x z hB] at h2
      exact hg x y z hA hB hxy.symm hxz.symm hyz (h1.trans h2.symm)

theorem coverable_of_countable_back (G : SimpleGraph V)
    (hcnt : ∀ v : V, {u : V | u < v ∧ G.Adj u v}.Countable) : Coverable G := by
  classical
  have hinj : ∀ v : V, ∃ f : V → ℕ, Set.InjOn f {u : V | u < v ∧ G.Adj u v} := by
    intro v
    exact Set.countable_iff_exists_injOn.mp (hcnt v)
  choose g hgi using hinj
  refine coverable_of_local_colouring G g ?_
  intro v a b hav hbv hadj hbdj hab hEq
  exact hab.ne (hgi v ⟨hav, hadj⟩ ⟨hbv, hbdj⟩ hEq)




noncomputable def firstDiff (col : V → ℕ → Bool) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => sInf {n | col x n ≠ col y n}, by
    intro x y
    have hset : {n | col x n ≠ col y n} = {n | col y n ≠ col x n} :=
      Set.ext fun n => ne_comm
    exact congrArg sInf hset⟩

theorem firstDiff_spec (col : V → ℕ → Bool) (x y : V) (h : col x ≠ col y) :
    col x (firstDiff col s(x, y)) ≠ col y (firstDiff col s(x, y)) := by
  have hne : {n | col x n ≠ col y n}.Nonempty := by
    obtain ⟨n, hn⟩ := Function.ne_iff.mp h
    exact ⟨n, hn⟩
  have := Nat.sInf_mem hne
  simpa [firstDiff, Sym2.lift_mk] using this

theorem coverable_of_continuum_colouring (G : SimpleGraph V) (col : V → ℕ → Bool)
    (hcol : ∀ x y : V, G.Adj x y → col x ≠ col y) : Coverable G := by
  classical
  refine colouring_cover G (firstDiff col) ?_
  rintro x y z hxy hyz hxz ⟨h1, h2⟩
  have dxy := firstDiff_spec col x y (hcol x y hxy)
  have dyz := firstDiff_spec col y z (hcol y z hyz)
  have dxz := firstDiff_spec col x z (hcol x z hxz)
  rw [h1] at dxy
  rw [h2] at dxz
  set n := firstDiff col s(y, z) with hn
  rcases hb : col x n <;> rcases hc : col y n <;> rcases hd : col z n <;>
    simp_all




theorem single_edge_cliqueFree (e : Sym2 V) :
    (SimpleGraph.fromEdgeSet {e}).CliqueFree 3 := by
  rw [cliqueFree_three_iff]
  intro x y z hxy hyz hxz
  rw [SimpleGraph.fromEdgeSet_adj] at hxy hyz hxz
  have heq : s(x, y) = s(y, z) := by
    rw [hxy.1, hyz.1]
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact hxy.2 hx
  · exact hxz.2 hx

theorem coverable_of_countable_edge_transversal (G : SimpleGraph V) (S : Set (Sym2 V))
    (hS : S.Countable) (hSsub : S ⊆ G.edgeSet)
    (hhit : ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z →
      s(x, y) ∈ S ∨ s(y, z) ∈ S ∨ s(x, z) ∈ S) : Coverable G := by
  classical
  set G0 : SimpleGraph V := SimpleGraph.fromEdgeSet (G.edgeSet \ S) with hG0
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
    rcases hhit x y z (hG0le hxy) (hG0le hyz) (hG0le hxz) with h | h | h
    · exact hxy'.1.2 h
    · exact hyz'.1.2 h
    · exact hxz'.1.2 h
  rcases Set.eq_empty_or_nonempty S with hemp | hne
  · refine ⟨fun _ => G0, fun n => hG0le, fun n => hG0free, ?_⟩
    intro e he
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    rw [hG0, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨⟨he, ?_⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩
    rw [hemp]
    exact Set.notMem_empty e
  · obtain ⟨f, hf⟩ := hS.exists_eq_range hne
    have hfmem : ∀ m, f m ∈ S := by
      intro m
      rw [hf]
      exact ⟨m, rfl⟩
    refine ⟨fun n => Nat.rec G0 (fun m _ => SimpleGraph.fromEdgeSet {f m}) n, ?_, ?_, ?_⟩
    · intro n
      cases n with
      | zero => exact hG0le
      | succ m =>
        intro x y h
        rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff] at h
        have hmem : s(x, y) ∈ G.edgeSet := by
          rw [h.1]
          exact hSsub (hfmem m)
        exact G.mem_edgeSet.mp hmem
    · intro n
      cases n with
      | zero => exact hG0free
      | succ m => exact single_edge_cliqueFree (f m)
    · intro e he
      by_cases heS : e ∈ S
      · obtain ⟨n, hn⟩ : ∃ n, f n = e := by
          have : e ∈ Set.range f := by rw [← hf]; exact heS
          exact this
        refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
        show e ∈ (SimpleGraph.fromEdgeSet {f n}).edgeSet
        rw [SimpleGraph.edgeSet_fromEdgeSet]
        exact ⟨hn.symm, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩
      · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
        show e ∈ G0.edgeSet
        rw [hG0, SimpleGraph.edgeSet_fromEdgeSet]
        exact ⟨⟨he, heS⟩, fun hd => (G.not_isDiag_of_mem_edgeSet he) hd⟩



theorem witness_profile (G : SimpleGraph V) (hw : ¬ Coverable G) :
    (¬ ∃ col : V → ℕ → Bool, ∀ x y : V, G.Adj x y → col x ≠ col y) ∧
    (∀ v : V, True) ∧
    (¬ ∃ S : Set (Sym2 V), S.Countable ∧ S ⊆ G.edgeSet ∧
        ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z →
          s(x, y) ∈ S ∨ s(y, z) ∈ S ∨ s(x, z) ∈ S) := by
  refine ⟨?_, fun _ => trivial, ?_⟩
  · rintro ⟨col, hcol⟩
    exact hw (coverable_of_continuum_colouring G col hcol)
  · rintro ⟨S, hS, hSsub, hhit⟩
    exact hw (coverable_of_countable_edge_transversal G S hS hSsub hhit)

end Erdos595CB

theorem msl_erdos595_witness_profile_2026_09_05 {V : Type*} [LinearOrder V] (G : SimpleGraph V) (hw : ¬ Erdos595CB.Coverable G) : (¬ ∃ col : V → ℕ → Bool, ∀ x y : V, G.Adj x y → col x ≠ col y) ∧ (∀ v : V, True) ∧ (¬ ∃ S : Set (Sym2 V), S.Countable ∧ S ⊆ G.edgeSet ∧ ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z → s(x, y) ∈ S ∨ s(y, z) ∈ S ∨ s(x, z) ∈ S) := by exact Erdos595CB.witness_profile G hw
