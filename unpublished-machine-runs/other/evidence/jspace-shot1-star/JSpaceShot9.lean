import Mathlib

/-! # JSPACE SHOT 9 — the doubling construction, in the kernel. -/

namespace JSpaceShot9

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

def HasS (T : Tournament V) (k : ℕ) : Prop :=
  ∀ A : Finset V, A.card ≤ k → (Dset T A).Nonempty

/-- Shot 9's load-bearing sublemma, stated verbatim. -/
def MixedResidual (T : Tournament V) (k : ℕ) : Prop :=
  ∀ AL AR : Finset V, AL.card + AR.card ≤ k + 1 → AL.card ≤ k →
    ∃ z, (∀ x ∈ AL, T.beats z x) ∧ (∀ y ∈ AR, z = y ∨ T.beats z y)

/-- **What the sublemma actually assumes.**  Taking `AL = ∅` it demands, of every set of
size `k+1`, a vertex that beats all of it (or lies in it and beats the rest).  The
hypothesis supplies only `S_k`. -/
theorem mixed_forces_kplus1 {T : Tournament V} {k : ℕ} (h : MixedResidual T k)
    (AR : Finset V) (hc : AR.card ≤ k + 1) :
    ∃ z, ∀ y ∈ AR, z = y ∨ T.beats z y := by
  obtain ⟨z, -, hz⟩ := h ∅ AR (by simpa using hc) (by simp)
  exact ⟨z, hz⟩

/-- Paley tournament on 7 vertices: `a → b` iff `b - a ∈ {1,2,4}`. -/
def P7 : Tournament (Fin 7) where
  beats a b := (b - a) = 1 ∨ (b - a) = 2 ∨ (b - a) = 4
  dec := inferInstance
  irrefl := by decide
  tot := by decide

set_option maxRecDepth 1000000 in
theorem P7_hasS : HasS P7 2 := by
  show ∀ A : Finset (Fin 7), A.card ≤ 2 → (Dset P7 A).Nonempty
  decide

set_option maxRecDepth 1000000 in
/-- `P7` has a 3-set that is beaten by nobody and contains no source of itself. -/
theorem P7_bad_triple :
    ∃ AR : Finset (Fin 7), AR.card = 3 ∧
      ∀ z : Fin 7, ¬ (∀ y ∈ AR, z = y ∨ P7.beats z y) := by decide

/-- **`mixed_residual_dominator` IS FALSE.**  `P7` has `S_2`, yet the sublemma fails
at `k = 2` with `AL = ∅`. -/
theorem mixed_residual_false : HasS P7 2 ∧ ¬ MixedResidual P7 2 := by
  refine ⟨P7_hasS, ?_⟩
  intro h
  obtain ⟨AR, hcard, hbad⟩ := P7_bad_triple
  obtain ⟨z, -, hz⟩ := h ∅ AR (by simp [hcard]) (by simp)
  exact hbad z hz

end JSpaceShot9

#print axioms JSpaceShot9.mixed_forces_kplus1
#print axioms JSpaceShot9.P7_hasS
#print axioms JSpaceShot9.P7_bad_triple
#print axioms JSpaceShot9.mixed_residual_false
