import Mathlib

set_option maxRecDepth 400000

/-! # JSPACE SYNTHESIS SHOT — the closed failure set and ABL, in the kernel. -/

namespace JSpaceSynth

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

/-- **(2), the graveyard correction.**  The CLOSED failure set. -/
def Fset (T : Tournament V) (Av : Finset V) (u : V) : Finset V :=
  Av.filter (fun a => a = u ∨ T.beats a u)

/-- The closed in-neighbourhood `C_v = N⁻(v) ∪ {v}`. -/
def Cset (T : Tournament V) (v : V) : Finset V :=
  insert v (univ.filter (fun x => T.beats x v))

theorem mem_Cset {T : Tournament V} {v x : V} :
    x ∈ Cset T v ↔ (x = v ∨ T.beats x v) := by simp [Cset]

/-- In a tournament, failing to be in `C_u` is exactly being beaten by `u`. -/
theorem not_mem_Cset {T : Tournament V} {u x : V} :
    x ∉ Cset T u ↔ T.beats u x := by
  rw [mem_Cset]
  constructor
  · intro h
    push_neg at h
    exact ((T.tot u x (Ne.symm h.1)).mpr h.2)
  · intro h
    push_neg
    refine ⟨fun hc => T.irrefl u (hc ▸ h), fun hc => ?_⟩
    exact ((T.tot u x (fun hc2 => T.irrefl x (hc2 ▸ h))).mp h) hc

/-! ## (4) — TRUE.  The exact identity, boundary included. -/

/-- **`closed_failure_iff`.**  `u ∈ D(A_v \ S) ↔ F_v(u) ⊆ S`, with no exception when
`u ∈ A_v`.  This is the repair of Shots 19 and 20. -/
theorem closed_failure_iff {T : Tournament V} (Av S : Finset V) (u : V) :
    u ∈ Dset T (Av \ S) ↔ Fset T Av u ⊆ S := by
  rw [mem_Dset]
  constructor
  · intro h a ha
    rw [Fset, Finset.mem_filter] at ha
    by_contra hS
    have hmem : a ∈ Av \ S := Finset.mem_sdiff.mpr ⟨ha.1, hS⟩
    have hbeat := h a hmem
    rcases ha.2 with rfl | hau
    · exact T.irrefl a hbeat
    · exact ((T.tot a u (fun hc => T.irrefl u (hc ▸ hau))).mp hau) hbeat
  · intro h a ha
    rw [Finset.mem_sdiff] at ha
    by_contra hc
    have : a ∈ Fset T Av u := by
      refine Finset.mem_filter.mpr ⟨ha.1, ?_⟩
      by_cases hau : a = u
      · exact Or.inl hau
      · exact Or.inr ((T.tot a u hau).mpr hc)
    exact ha.2 (h this)

/-- **(3) — TRUE.**  `F_v(v) = ∅` for a critical set. -/
theorem Fset_self_empty {T : Tournament V} {Av : Finset V} {v : V}
    (hcrit : Dset T Av = {v}) : Fset T Av v = ∅ := by
  have hv : v ∈ Dset T Av := by rw [hcrit]; exact Finset.mem_singleton_self v
  refine Finset.eq_empty_iff_forall_notMem.mpr (fun a ha => ?_)
  rw [Fset, Finset.mem_filter] at ha
  have hbeat := mem_Dset.mp hv a ha.1
  rcases ha.2 with rfl | hav
  · exact T.irrefl a hbeat
  · exact ((T.tot a v (fun hc => T.irrefl v (hc ▸ hav))).mp hav) hbeat

/-- **(3) — TRUE.**  `F_v(u) ≠ ∅` for every `u ≠ v`, INCLUDING `u ∈ A_v`. -/
theorem Fset_nonempty_of_ne {T : Tournament V} {Av : Finset V} {v u : V}
    (hcrit : Dset T Av = {v}) (hu : u ≠ v) : (Fset T Av u).Nonempty := by
  have hnot : u ∉ Dset T Av := by rw [hcrit, Finset.mem_singleton]; exact hu
  rw [mem_Dset] at hnot
  push_neg at hnot
  obtain ⟨a, haA, hab⟩ := hnot
  refine ⟨a, Finset.mem_filter.mpr ⟨haA, ?_⟩⟩
  by_cases hau : a = u
  · exact Or.inl hau
  · exact Or.inr ((T.tot a u hau).mpr hab)

/-! ## What ABL actually assumes. -/

theorem cross_iff_not_dominates {T : Tournament V} (Av : Finset V) (u : V) :
    (Av ∩ Cset T u).Nonempty ↔ u ∉ Dset T Av := by
  constructor
  · rintro ⟨a, ha⟩
    rw [Finset.mem_inter] at ha
    intro hu
    exact (not_mem_Cset.mpr (mem_Dset.mp hu a ha.1)) ha.2
  · intro hu
    rw [mem_Dset] at hu
    push_neg at hu
    obtain ⟨a, haA, hab⟩ := hu
    exact ⟨a, Finset.mem_inter.mpr ⟨haA, by
      by_contra hc
      exact hab (not_mem_Cset.mp hc)⟩⟩

theorem diag_iff_dominates {T : Tournament V} (Av : Finset V) (v : V) :
    Disjoint Av (Cset T v) ↔ v ∈ Dset T Av := by
  rw [Finset.disjoint_left, mem_Dset]
  constructor
  · intro h a ha
    exact not_mem_Cset.mp (h ha)
  · intro h a ha
    exact not_mem_Cset.mpr (h a ha)

/-- **ABL is not a lemma toward the theorem; its hypotheses ARE criticality.**
`A_i ∩ C_i = ∅` says `i` dominates `A_i`; `A_i ∩ C_j ≠ ∅` for `j ≠ i` says nobody else
does.  Together they are exactly `D(A_i) = {i}`.  So `antisymmetric_bollobas` states
`f(k) ≤ (k+1)·2^k`, which is the open upper bound itself. -/
theorem abl_hypotheses_are_criticality {T : Tournament V} (Av : Finset V) (v : V) :
    (Disjoint Av (Cset T v) ∧ ∀ u : V, u ≠ v → (Av ∩ Cset T u).Nonempty)
      ↔ Dset T Av = {v} := by
  constructor
  · rintro ⟨hd, hc⟩
    have hv : v ∈ Dset T Av := (diag_iff_dominates Av v).mp hd
    ext x
    rw [Finset.mem_singleton]
    constructor
    · intro hx
      by_contra hne
      exact ((cross_iff_not_dominates Av x).mp (hc x hne)) hx
    · intro hx; exact hx ▸ hv
  · intro hcrit
    refine ⟨(diag_iff_dominates Av v).mpr (by rw [hcrit]; exact Finset.mem_singleton_self v), ?_⟩
    intro u hu
    refine (cross_iff_not_dominates Av u).mpr ?_
    rw [hcrit, Finset.mem_singleton]
    exact hu

/-! ## The permutation proof of ABL. -/

/-- **(11) points the wrong way.**  `E_v` is the conjunction of three clauses, the third
being "`v` is first in `π` among its signature class".  Adding a clause can only shrink
an event, so it cannot support a LOWER bound on `Pr(E_v)`.  The count `1/((k+1)2^k)` is
the probability of the first two clauses alone. -/
theorem third_clause_wrong_direction {α : Type*} [Fintype α] [DecidableEq α]
    (p q r : α → Prop) [DecidablePred p] [DecidablePred q] [DecidablePred r] :
    (univ.filter (fun x => p x ∧ q x ∧ r x)).card
      ≤ (univ.filter (fun x => p x ∧ q x)).card := by
  refine Finset.card_le_card (fun x hx => ?_)
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1, hx.2.2.1⟩

end JSpaceSynth

#print axioms JSpaceSynth.closed_failure_iff
#print axioms JSpaceSynth.Fset_self_empty
#print axioms JSpaceSynth.Fset_nonempty_of_ne
#print axioms JSpaceSynth.cross_iff_not_dominates
#print axioms JSpaceSynth.abl_hypotheses_are_criticality
#print axioms JSpaceSynth.third_clause_wrong_direction
