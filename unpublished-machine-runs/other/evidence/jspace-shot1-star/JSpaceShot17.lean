import Mathlib

set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

/-! # JSPACE SHOT 17 — the certificate-signature lemma (3), in the kernel. -/

namespace JSpaceShot17

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

/-- Signature of `v` against `M`. -/
def Lset (T : Tournament V) (M : Finset V) (v : V) : Finset V :=
  M.filter (fun x => T.beats x v)

/-- `R(S) = {v : L(v) ⊆ S}`, exactly as Shot 17 defines it. -/
def Rset (T : Tournament V) (M S : Finset V) : Finset V :=
  univ.filter (fun v => Lset T M v ⊆ S)

def IsDominating (T : Tournament V) (Q : Finset V) : Prop :=
  ∀ v : V, v ∉ Q → ∃ x ∈ Q, T.beats x v

def IsMinimumDominating (T : Tournament V) (M : Finset V) : Prop :=
  IsDominating T M ∧ ∀ Q : Finset V, IsDominating T Q → M.card ≤ Q.card

def IsDominatingIn (T : Tournament V) (W Q : Finset V) : Prop :=
  Q ⊆ W ∧ ∀ v ∈ W, v ∉ Q → ∃ x ∈ Q, T.beats x v

def IsMinimumDominatingIn (T : Tournament V) (W Q : Finset V) : Prop :=
  IsDominatingIn T W Q ∧ ∀ Q' : Finset V, IsDominatingIn T W Q' → Q.card ≤ Q'.card

/-- `w` is a private witness for `q` inside `Q`: it lies in the residual, is not in `Q`,
`q` beats it, and nothing else in `Q` beats it. -/
def PrivateWitnessIn (T : Tournament V) (W Q : Finset V) (q w : V) : Prop :=
  w ∈ W ∧ w ∉ Q ∧ T.beats q w ∧ ∀ z ∈ Q, z ≠ q → ¬ T.beats z w

/-! ## The witness. -/

/-- `T8`: Paley-7 on `{0,…,6}` plus a vertex `7` beaten by `{3,4,5,6}` and beating
`{0,1,2}`.  It has `S_2`, hence `γ(T8) = 3`. -/
def T8 : Tournament (Fin 8) where
  beats a b :=
    if a.val = 7 then b.val < 3
    else if b.val = 7 then 3 ≤ a.val ∧ a.val < 7
    else ((b.val + 7 - a.val) % 7 = 1 ∨ (b.val + 7 - a.val) % 7 = 2 ∨
          (b.val + 7 - a.val) % 7 = 4)
  dec := inferInstance
  irrefl := by decide
  tot := by decide

def M8 : Finset (Fin 8) := {0, 1, 6}

theorem M8_min : IsMinimumDominating T8 M8 := by
  constructor
  · show ∀ v : Fin 8, v ∉ M8 → ∃ x ∈ M8, T8.beats x v
    decide
  · show ∀ Q : Finset (Fin 8),
      (∀ v : Fin 8, v ∉ Q → ∃ x ∈ Q, T8.beats x v) → M8.card ≤ Q.card
    decide

/-- With `S = M`, the residual `R(S)` is everything, and `M` is a minimum dominating set
of it. -/
theorem Rset_M8 : Rset T8 M8 M8 = univ := by decide

theorem Q8_min : IsMinimumDominatingIn T8 (Rset T8 M8 M8) M8 := by
  constructor
  · show M8 ⊆ Rset T8 M8 M8 ∧ ∀ v ∈ Rset T8 M8 M8, v ∉ M8 → ∃ x ∈ M8, T8.beats x v
    decide
  · show ∀ Q' : Finset (Fin 8),
      (Q' ⊆ Rset T8 M8 M8 ∧ ∀ v ∈ Rset T8 M8 M8, v ∉ Q' → ∃ x ∈ Q', T8.beats x v) →
      M8.card ≤ Q'.card
    decide

/-- `7` is a private witness for `6`. -/
theorem w8_private : PrivateWitnessIn T8 (Rset T8 M8 M8) M8 6 7 := by
  show (7 : Fin 8) ∈ Rset T8 M8 M8 ∧ (7 : Fin 8) ∉ M8 ∧ T8.beats 6 7 ∧
    ∀ z ∈ M8, z ≠ 6 → ¬ T8.beats z 7
  decide

/-- The certificate signature is tiny: `L(6) = ∅`, `L(7) = {6}`, union of size `1`. -/
theorem signature_small :
    (Lset T8 M8 6 ∪ Lset T8 M8 7).card = 1 ∧ M8.card = 3 := by decide

/-- **(3) IS FALSE.**  Every hypothesis of `certificate_union_codim_one` holds and
`|S| = 3 > 2 = |L(q) ∪ L(w)| + 1`. -/
theorem certificate_union_codim_one_false :
    IsMinimumDominating T8 M8 ∧
    M8 ⊆ M8 ∧
    IsMinimumDominatingIn T8 (Rset T8 M8 M8) M8 ∧
    (6 : Fin 8) ∈ M8 ∧
    PrivateWitnessIn T8 (Rset T8 M8 M8) M8 6 7 ∧
    ¬ (M8.card ≤ (Lset T8 M8 6 ∪ Lset T8 M8 7).card + 1) := by
  refine ⟨M8_min, Finset.Subset.refl _, Q8_min, by decide, w8_private, ?_⟩
  obtain ⟨h1, h2⟩ := signature_small
  rw [h1, h2]
  decide

end JSpaceShot17

#print axioms JSpaceShot17.M8_min
#print axioms JSpaceShot17.Q8_min
#print axioms JSpaceShot17.w8_private
#print axioms JSpaceShot17.certificate_union_codim_one_false
