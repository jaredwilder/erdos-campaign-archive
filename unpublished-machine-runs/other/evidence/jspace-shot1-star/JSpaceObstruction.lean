import Mathlib

set_option maxRecDepth 400000

/-! # JSPACE OBSTRUCTION PASS — the structural lift and the crown, in the kernel. -/

namespace JSpaceObs

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

def Dset (T : Tournament V) (A : Finset V) : Finset V :=
  univ.filter (fun v => ∀ a ∈ A, T.beats v a)

theorem mem_Dset {T : Tournament V} {A : Finset V} {v : V} :
    v ∈ Dset T A ↔ ∀ a ∈ A, T.beats v a := by simp [Dset]

def HasS (T : Tournament V) (k : ℕ) : Prop :=
  ∀ A : Finset V, A.card ≤ k → (Dset T A).Nonempty

def IsDominating (T : Tournament V) (Q : Finset V) : Prop :=
  ∀ u : V, u ∉ Q → ∃ x ∈ Q, T.beats x u

def IsMinimumDominating (T : Tournament V) (M : Finset V) : Prop :=
  IsDominating T M ∧ ∀ Q : Finset V, IsDominating T Q → M.card ≤ Q.card

/-- In a tournament, `¬ beats x u` with `x ≠ u` gives `beats u x`. -/
theorem beats_of_not {T : Tournament V} {x u : V} (hne : u ≠ x) (h : ¬ T.beats x u) :
    T.beats u x := by
  by_contra hc
  exact h ((T.tot x u (Ne.symm hne)).mpr hc)

/-! ## `S_k` bounds the domination number below. -/

/-- `S_k` says no set of size `≤ k` dominates. -/
theorem no_small_dominating {T : Tournament V} {k : ℕ} (hS : HasS T k)
    {Q : Finset V} (hQ : Q.card ≤ k) : ¬ IsDominating T Q := by
  intro hdom
  obtain ⟨w, hw⟩ := hS Q hQ
  have hbeat := mem_Dset.mp hw
  have hwQ : w ∉ Q := fun hc => T.irrefl w (hbeat w hc)
  obtain ⟨x, hxQ, hxw⟩ := hdom w hwQ
  exact ((T.tot w x (fun hc => hwQ (hc ▸ hxQ))).mp (hbeat x hxQ)) hxw

/-! ## Fire point 1 — TRUE. -/

/-- **`critical_union_is_min_dom`.**  If `D(A_v) = {v}` and `|A_v| = k` then
`{v} ∪ A_v` is a minimum dominating set, of size exactly `k+1`.
So `γ(T) = k+1`, and every vertex is the source of a minimum dominating set. -/
theorem critical_union_is_min_dom {T : Tournament V} {k : ℕ} {Av : Finset V} {v : V}
    (hS : HasS T k) (hcrit : Dset T Av = {v}) (hcard : Av.card = k) :
    IsMinimumDominating T (insert v Av) := by
  have hvD : v ∈ Dset T Av := by rw [hcrit]; exact Finset.mem_singleton_self v
  have hvA : v ∉ Av := fun hc => T.irrefl v (mem_Dset.mp hvD v hc)
  constructor
  · intro u hu
    rw [Finset.mem_insert] at hu
    push_neg at hu
    have hunD : u ∉ Dset T Av := by rw [hcrit, Finset.mem_singleton]; exact hu.1
    rw [mem_Dset] at hunD
    push_neg at hunD
    obtain ⟨a, haA, hab⟩ := hunD
    exact ⟨a, Finset.mem_insert_of_mem haA, beats_of_not (fun hc => hu.2 (hc ▸ haA)) hab⟩
  · intro Q hQ
    rw [Finset.card_insert_of_notMem hvA, hcard]
    by_contra hc
    push_neg at hc
    exact (no_small_dominating hS (by omega)) hQ

/-! ## Fire point 2 — TRUE. -/

/-- **`critical_private_crown`.**  Every `a ∈ A_v` has a private witness `p a` outside
`{v} ∪ A_v`, with the crown orientation `v → a → p a → v` and `p a → b` for every other
`b ∈ A_v`.  The assignment is injective on `A_v` automatically. -/
theorem critical_private_crown {T : Tournament V} {k : ℕ} {Av : Finset V} {v : V}
    (hS : HasS T k) (hcrit : Dset T Av = {v}) (hcard : Av.card = k) :
    ∃ p : V → V,
      (∀ a ∈ Av, p a ∉ insert v Av) ∧
      (∀ a ∈ Av, T.beats a (p a)) ∧
      (∀ a ∈ Av, T.beats (p a) v) ∧
      (∀ a ∈ Av, ∀ b ∈ Av, b ≠ a → T.beats (p a) b) ∧
      (∀ a ∈ Av, ∀ b ∈ Av, a ≠ b → p a ≠ p b) := by
  have hvD : v ∈ Dset T Av := by rw [hcrit]; exact Finset.mem_singleton_self v
  have hvA : v ∉ Av := fun hc => T.irrefl v (mem_Dset.mp hvD v hc)
  have hMcard : (insert v Av).card = k + 1 := by
    rw [Finset.card_insert_of_notMem hvA, hcard]
  have hMdom : IsDominating T (insert v Av) :=
    (critical_union_is_min_dom hS hcrit hcard).1
  -- the private witness exists for each a ∈ Av
  have key : ∀ a : V, ∃ w : V, a ∈ Av →
      (w ∉ insert v Av ∧ T.beats a w ∧ T.beats w v ∧
        ∀ b ∈ Av, b ≠ a → T.beats w b) := by
    intro a
    by_cases haA : a ∈ Av
    · -- erasing a leaves k vertices, too few to dominate
      have herase : ((insert v Av).erase a).card ≤ k := by
        rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem haA), hMcard]
        omega
      have hnd := no_small_dominating hS herase
      unfold IsDominating at hnd
      push_neg at hnd
      obtain ⟨w, hwn, hw⟩ := hnd
      have hva : v ≠ a := fun hc => hvA (hc ▸ haA)
      have hvmem : v ∈ (insert v Av).erase a :=
        Finset.mem_erase.mpr ⟨hva, Finset.mem_insert_self _ _⟩
      -- w is not in the full set either
      have hwM : w ∉ insert v Av := by
        intro hcM
        rcases Finset.mem_insert.mp hcM with rfl | hwA
        · exact hwn hvmem
        · by_cases hwa : w = a
          · exact hw v hvmem (by rw [hwa]; exact mem_Dset.mp hvD a haA)
          · exact hwn (Finset.mem_erase.mpr ⟨hwa, Finset.mem_insert_of_mem hwA⟩)
      obtain ⟨x, hxM, hxw⟩ := hMdom w hwM
      have hxa : x = a := by
        by_contra hxa
        exact hw x (Finset.mem_erase.mpr ⟨hxa, hxM⟩) hxw
      subst hxa
      refine ⟨w, fun _ => ⟨hwM, hxw, ?_, ?_⟩⟩
      · exact beats_of_not (fun hc => hwM (hc ▸ Finset.mem_insert_self _ _))
          (hw v hvmem)
      · intro b hbA hba
        exact beats_of_not (fun hc => hwM (hc ▸ Finset.mem_insert_of_mem hbA))
          (hw b (Finset.mem_erase.mpr ⟨hba, Finset.mem_insert_of_mem hbA⟩))
    · refine ⟨a, ?_⟩
      intro hc
      exact absurd hc haA
  choose p hp using key
  refine ⟨p, fun a ha => (hp a ha).1, fun a ha => (hp a ha).2.1,
    fun a ha => (hp a ha).2.2.1, fun a ha b hb hba => (hp a ha).2.2.2 b hb hba, ?_⟩
  -- injectivity is forced by the crown orientation
  intro a ha b hb hab hpeq
  have h1 : T.beats b (p b) := (hp b hb).2.1
  have h2 : T.beats (p a) b := (hp a ha).2.2.2 b hb (Ne.symm hab)
  rw [hpeq] at h2
  exact ((T.tot b (p b) (fun hc => T.irrefl (p b) (hc ▸ h1))).mp h1) h2

end JSpaceObs

#print axioms JSpaceObs.no_small_dominating
#print axioms JSpaceObs.critical_union_is_min_dom
#print axioms JSpaceObs.critical_private_crown
