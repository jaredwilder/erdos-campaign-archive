import Mathlib

/-! # JSPACE SHOT 11 — the dichotomy DICH, in the kernel. -/

namespace JSpaceShot11

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

/-- `T[S]` is strongly connected: no proper nonempty `X ⊆ S` beats all of `S \ X`. -/
def IsStrongOn (T : Tournament V) (S : Finset V) : Prop :=
  ∀ X : Finset V, X ⊆ S → X.Nonempty → X ≠ S → ∃ x ∈ X, ∃ y ∈ S \ X, T.beats y x

instance decIsStrongOn (T : Tournament V) : DecidablePred (IsStrongOn T) := by
  intro S; unfold IsStrongOn; infer_instance

/-- The number of strongly connected `r`-subsets. -/
def strongRCount (T : Tournament V) (r : ℕ) : ℕ :=
  ((powersetCard r (univ : Finset V)).filter (fun S => IsStrongOn T S)).card

/-- A dominant split: a nonempty proper `X` beating everything outside it. -/
def HasDominantSplit (T : Tournament V) : Prop :=
  ∃ X : Finset V, X.Nonempty ∧ X ≠ univ ∧ ∀ x ∈ X, ∀ y ∈ univ \ X, T.beats x y

instance decHasDominantSplit (T : Tournament V) : Decidable (HasDominantSplit T) := by
  unfold HasDominantSplit; infer_instance

/-- **The reduction.**  A transitive module partition `V₁ → ⋯ → V_t` with `t ≥ 2` has
`X = V₁` beating everything outside it, so DICH's second alternative implies
`HasDominantSplit`.  Refuting the version below therefore refutes DICH. -/
theorem dominant_split_of_first_part {T : Tournament V} {X : Finset V}
    (hne : X.Nonempty) (hproper : X ≠ univ)
    (h : ∀ x ∈ X, ∀ y ∈ univ \ X, T.beats x y) : HasDominantSplit T :=
  ⟨X, hne, hproper, h⟩

/-- DICH, with the second alternative weakened as above. -/
def DICH (T : Tournament V) (r : ℕ) : Prop :=
  Nat.choose (Fintype.card V) r ≤ 4 * strongRCount T r ∨ HasDominantSplit T

/-! ## The witness. -/

/-- `T6`: the transitive order `0 < 1 < ⋯ < 5` with the single edge `5 → 0` reversed.
The Hamiltonian cycle `0→1→2→3→4→5→0` makes it strongly connected. -/
def T6 : Tournament (Fin 6) where
  beats a b :=
    (a.val = 5 ∧ b.val = 0) ∨ (¬(a.val = 0 ∧ b.val = 5) ∧ a.val < b.val)
  dec := inferInstance
  irrefl := by decide
  tot := by decide

/-- `T6` has no dominant split, hence no transitive module partition into `≥ 2` parts. -/
theorem T6_no_split : ¬ HasDominantSplit T6 := by decide

/-- Only the four triples `{0, b, 5}` are strongly connected, out of `C(6,3) = 20`. -/
theorem T6_count : strongRCount T6 3 = 4 := by decide

/-- **DICH IS FALSE.**  `T6` is strongly connected, so the second alternative fails,
and `4 · 4 = 16 < 20 = C(6,3)`, so the first fails too. -/
theorem DICH_false : 3 ≤ 3 ∧ (3 : ℕ) ≤ Fintype.card (Fin 6) ∧ ¬ DICH T6 3 := by
  refine ⟨le_refl 3, by decide, ?_⟩
  rintro (h | h)
  · rw [T6_count] at h
    revert h
    decide
  · exact T6_no_split h

end JSpaceShot11

#print axioms JSpaceShot11.dominant_split_of_first_part
#print axioms JSpaceShot11.T6_no_split
#print axioms JSpaceShot11.T6_count
#print axioms JSpaceShot11.DICH_false
