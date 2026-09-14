import Mathlib

set_option maxRecDepth 400000

/-! # JSPACE SHOT 20 — the critical-pair inequality (8), in the kernel. -/

namespace JSpaceShot20

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

def DsetIn (T : Tournament V) (W A : Finset V) : Finset V :=
  W.filter (fun v => ∀ a ∈ A, T.beats v a)

def HasS (T : Tournament V) (k : ℕ) : Prop :=
  ∀ A : Finset V, A.card ≤ k → (Dset T A).Nonempty

def HasSIn (T : Tournament V) (W : Finset V) (k : ℕ) : Prop :=
  ∀ A : Finset V, A ⊆ W → A.card ≤ k → (DsetIn T W A).Nonempty

/-- `t_{vw} = |{a ∈ A_v : a → w}|`, the failure count. -/
def tcount (T : Tournament V) (Av : Finset V) (w : V) : ℕ :=
  (Av.filter (fun a => T.beats a w)).card

/-- Paley-7. `f(2) = 7`, so Paley-7 is an order-minimal `S_2` tournament. -/
def P7 : Tournament (Fin 7) where
  beats a b := ((b.val + 7 - a.val) % 7) ∈ ({1, 2, 4} : Finset ℕ)
  dec := inferInstance
  irrefl := by decide
  tot := by decide

theorem P7_hasS : HasS P7 2 := by
  show ∀ A : Finset (Fin 7), A.card ≤ 2 → (Dset P7 A).Nonempty
  decide

/-- Order-minimality: deleting any vertex destroys `S_2`. -/
theorem P7_hmin : ∀ v : Fin 7, ¬ HasSIn P7 (univ.erase v) 2 := by
  show ∀ v : Fin 7, ¬ ∀ A : Finset (Fin 7), A ⊆ univ.erase v → A.card ≤ 2 →
    (DsetIn P7 (univ.erase v) A).Nonempty
  decide

/-- In Paley-7 every pair has exactly one dominator, so every pair is critical.
`{1,2}` is critical for `0`; `{1,4}` is critical for `0`; `{2,3}` is critical for `1`. -/
theorem P7_criticals :
    Dset P7 {1, 2} = {0} ∧ Dset P7 {1, 4} = {0} ∧ Dset P7 {2, 3} = {1} := by decide

/-- **(8) IS FALSE.**  With `A_0 = {1,2}` and `A_1 = {2,3}`, both critical,
`t_{01} + t_{10} = 0 + 1 = 1 < 2 = k`. -/
theorem critical_pair_failure_sum_false :
    HasS P7 2 ∧
    (∀ v : Fin 7, ¬ HasSIn P7 (univ.erase v) 2) ∧
    Dset P7 {1, 2} = {0} ∧ Dset P7 {2, 3} = {1} ∧
    ({1, 2} : Finset (Fin 7)).card = 2 ∧ ({2, 3} : Finset (Fin 7)).card = 2 ∧
    (0 : Fin 7) ≠ 1 ∧
    tcount P7 {1, 2} 1 = 0 ∧ tcount P7 {2, 3} 0 = 1 ∧
    ¬ (2 ≤ tcount P7 {1, 2} 1 + tcount P7 {2, 3} 0) := by
  refine ⟨P7_hasS, P7_hmin, ?_⟩
  decide

/-- **(17) IS FALSE TOO.**  With `A_0 = {1,4}` and `A_1 = {2,3}`, both critical,
`t_{01} = t_{10} = 1`, so the minimum is `1` while the maximum is `1 < k = 2`.
(17) demands the maximum be at least `k`. -/
theorem eq17_false :
    Dset P7 {1, 4} = {0} ∧ Dset P7 {2, 3} = {1} ∧
    tcount P7 {1, 4} 1 = 1 ∧ tcount P7 {2, 3} 0 = 1 ∧
    ¬ (2 ≤ max (tcount P7 {1, 4} 1) (tcount P7 {2, 3} 0)) := by decide

/-- The full failure profile of vertex `0` against `A_0 = {1,2}`, showing `t_{0,1} = 0`:
Shot 20's (3) again asserts `F_v(w) ≠ ∅` for `w ≠ v`, and again the members of `A_v`
are the exception. -/
theorem P7_failure_profile :
    tcount P7 {1, 2} 0 = 0 ∧ tcount P7 {1, 2} 1 = 0 ∧ tcount P7 {1, 2} 2 = 1 ∧
    tcount P7 {1, 2} 3 = 2 ∧ tcount P7 {1, 2} 4 = 1 ∧ tcount P7 {1, 2} 5 = 1 ∧
    tcount P7 {1, 2} 6 = 1 := by decide

end JSpaceShot20

#print axioms JSpaceShot20.P7_hasS
#print axioms JSpaceShot20.P7_hmin
#print axioms JSpaceShot20.P7_criticals
#print axioms JSpaceShot20.critical_pair_failure_sum_false
#print axioms JSpaceShot20.eq17_false
#print axioms JSpaceShot20.P7_failure_profile
