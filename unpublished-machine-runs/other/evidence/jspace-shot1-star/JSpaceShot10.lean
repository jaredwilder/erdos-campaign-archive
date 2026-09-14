import Mathlib

/-! # JSPACE SHOT 10 — the quotient theorem, in the kernel. -/

namespace JSpaceShot10

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

/-- Dominators of `A` drawn from inside `W`. -/
def DsetIn (T : Tournament V) (W A : Finset V) : Finset V :=
  W.filter (fun v => ∀ a ∈ A, T.beats v a)

/-- `S_k` for the tournament induced on `W`. -/
def HasSIn (T : Tournament V) (W : Finset V) (k : ℕ) : Prop :=
  ∀ A : Finset V, A ⊆ W → A.card ≤ k → (DsetIn T W A).Nonempty

/-- `S_k` for the whole tournament. -/
def HasS (T : Tournament V) (k : ℕ) : Prop := HasSIn T univ k

/-- `M` is a module: every outside vertex sees all of `M` the same way. -/
def IsModule (T : Tournament V) (M : Finset V) : Prop :=
  ∀ z, z ∉ M → ∀ x ∈ M, ∀ y ∈ M, (T.beats z x ↔ T.beats z y)

/-- Contracting the module `M` to the single representative `m₀`: the quotient is the
tournament induced on `(V \ M) ∪ {m₀}`. -/
def quotientCarrier (M : Finset V) (m₀ : V) : Finset V := (univ \ M) ∪ {m₀}

/-! ## `quotient_preserves_S` is FALSE. -/

/-- **The general mechanism.**  If the module `M` beats everything outside it, then the
contracted vertex has no in-neighbour in the quotient, so the quotient loses `S_k` for
every `k ≥ 1` — no matter how large `k` is, and no matter that `T` itself has `S_k`. -/
theorem quotient_loses_S {T : Tournament V} {M : Finset V} {m₀ : V} {k : ℕ}
    (hm₀ : m₀ ∈ M) (hout : ∀ z, z ∉ M → ∀ x ∈ M, T.beats x z) (hk : 1 ≤ k) :
    ¬ HasSIn T (quotientCarrier M m₀) k := by
  intro h
  have hsub : ({m₀} : Finset V) ⊆ quotientCarrier M m₀ := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  obtain ⟨v, hv⟩ := h {m₀} hsub (by simpa using hk)
  rw [DsetIn, Finset.mem_filter] at hv
  obtain ⟨hvW, hvbeat⟩ := hv
  have hvm : T.beats v m₀ := hvbeat m₀ (Finset.mem_singleton_self _)
  rcases Finset.mem_union.mp hvW with hv1 | hv1
  · -- v lies outside M, so m₀ beats v, contradicting v beats m₀
    have hvM : v ∉ M := (Finset.mem_sdiff.mp hv1).2
    have hne : m₀ ≠ v := fun hc => hvM (hc ▸ hm₀)
    exact ((T.tot m₀ v hne).mp (hout v hvM m₀ hm₀)) hvm
  · -- v = m₀, contradicting irreflexivity
    rw [Finset.mem_singleton] at hv1
    subst hv1
    exact T.irrefl v hvm

/-! ## A concrete instance. -/

/-- `T4`: the 3-cycle `0 → 1 → 2 → 0` on `M = {0,1,2}`, with `3` beaten by all of `M`. -/
def T4 : Tournament (Fin 4) where
  beats a b :=
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a ≠ 3 ∧ b = 3)
  dec := inferInstance
  irrefl := by decide
  tot := by decide

theorem T4_hasS : HasS T4 1 := by
  show ∀ A : Finset (Fin 4), A ⊆ univ → A.card ≤ 1 → (DsetIn T4 univ A).Nonempty
  decide

theorem T4_module : IsModule T4 ({0, 1, 2} : Finset (Fin 4)) := by
  show ∀ z : Fin 4, z ∉ ({0,1,2} : Finset (Fin 4)) →
    ∀ x ∈ ({0,1,2} : Finset (Fin 4)), ∀ y ∈ ({0,1,2} : Finset (Fin 4)),
      (T4.beats z x ↔ T4.beats z y)
  decide

theorem T4_module_nontrivial :
    ({0, 1, 2} : Finset (Fin 4)).card = 3 ∧ Fintype.card (Fin 4) = 4 := by decide

theorem T4_out : ∀ z : Fin 4, z ∉ ({0,1,2} : Finset (Fin 4)) →
    ∀ x ∈ ({0,1,2} : Finset (Fin 4)), T4.beats x z := by decide

/-- **`quotient_preserves_S` IS FALSE.**  `T4` has `S_1`, `{0,1,2}` is a nontrivial
module, and contracting it destroys `S_1`. -/
theorem quotient_preserves_S_false :
    HasS T4 1 ∧
    IsModule T4 ({0, 1, 2} : Finset (Fin 4)) ∧
    ¬ HasSIn T4 (quotientCarrier ({0, 1, 2} : Finset (Fin 4)) 0) 1 :=
  ⟨T4_hasS, T4_module, quotient_loses_S (by decide) T4_out (le_refl 1)⟩

end JSpaceShot10

#print axioms JSpaceShot10.quotient_loses_S
#print axioms JSpaceShot10.T4_hasS
#print axioms JSpaceShot10.T4_module
#print axioms JSpaceShot10.quotient_preserves_S_false
