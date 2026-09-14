import Mathlib

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-! # JSPACE SHOT 18 — the minimality invariant and the singleton-residual bound. -/

namespace JSpaceShot18

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

def DsetIn (T : Tournament V) (W A : Finset V) : Finset V :=
  W.filter (fun v => ∀ a ∈ A, T.beats v a)

def HasS (T : Tournament V) (k : ℕ) : Prop :=
  ∀ A : Finset V, A.card ≤ k → (Dset T A).Nonempty

def HasSIn (T : Tournament V) (W : Finset V) (k : ℕ) : Prop :=
  ∀ A : Finset V, A ⊆ W → A.card ≤ k → (DsetIn T W A).Nonempty

/-- `S_k` forces `k < N`: otherwise `A = univ` would need a dominator beating itself. -/
theorem card_gt_of_HasS {T : Tournament V} {k : ℕ} (h : HasS T k) :
    k < Fintype.card V := by
  by_contra hc
  push_neg at hc
  obtain ⟨v, hv⟩ := h univ (by simpa using hc)
  exact T.irrefl v (mem_Dset.mp hv v (Finset.mem_univ v))

/-! ## Fire point 1 — TRUE. -/

/-- **`deletion_gives_unique_dominator`.**  If `T` has `S_k` and deleting any single
vertex destroys it, then every vertex is the unique dominator of some `k`-set. -/
theorem deletion_gives_unique_dominator {T : Tournament V} {k : ℕ}
    (hS : HasS T k) (hmin : ∀ v : V, ¬ HasSIn T (univ.erase v) k) (v : V) :
    ∃ A : Finset V, A.card = k ∧ v ∉ A ∧ Dset T A = {v} := by
  -- the deleted tournament fails S_k on some small set
  have h := hmin v
  unfold HasSIn at h
  push_neg at h
  obtain ⟨A₀, hA₀sub, hA₀card, hA₀empty⟩ := h
  -- extend it to a k-set still avoiding v
  have hkle : k ≤ (univ.erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    have := card_gt_of_HasS hS
    omega
  obtain ⟨A, hA0A, hAsub, hAcard⟩ :=
    Finset.exists_subsuperset_card_eq hA₀sub hA₀card hkle
  refine ⟨A, hAcard, fun hv => (Finset.mem_erase.mp (hAsub hv)).1 rfl, ?_⟩
  -- every dominator of A must be v
  obtain ⟨u, hu⟩ := hS A (le_of_eq hAcard)
  have huA₀ : ∀ w, w ∈ Dset T A → w = v := by
    intro w hw
    by_contra hne
    have hwerase : w ∈ univ.erase v := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ w⟩
    have : w ∈ DsetIn T (univ.erase v) A₀ :=
      Finset.mem_filter.mpr ⟨hwerase, fun a ha => mem_Dset.mp hw a (hA0A ha)⟩
    rw [hA₀empty] at this
    exact absurd this (Finset.notMem_empty w)
  have hv : v ∈ Dset T A := by rw [← huA₀ u hu]; exact hu
  ext x
  simp only [Finset.mem_singleton]
  exact ⟨huA₀ x, fun hx => hx ▸ hv⟩

/-! ## Fire point 2 — the singleton-residual count. -/

/-- `Z₁ = #{A : |A| = k, |D(A)| = 1}`. -/
def Z1 (T : Tournament V) (k : ℕ) : ℕ :=
  ((powersetCard k (univ : Finset V)).filter (fun A => (Dset T A).card = 1)).card

def P7 : Tournament (Fin 7) where
  beats a b := ((b.val + 7 - a.val) % 7) ∈ ({1, 2, 4} : Finset ℕ)
  dec := inferInstance
  irrefl := by decide
  tot := by decide

def P19 : Tournament (Fin 19) where
  beats a b := ((b.val + 19 - a.val) % 19) ∈ ({1, 4, 5, 6, 7, 9, 11, 16, 17} : Finset ℕ)
  dec := inferInstance
  irrefl := by decide
  tot := by decide

#eval Z1 P7 2
#eval Z1 P19 3

/-- `f(2) = 7`, and Paley-7 is the extremal `S_2` tournament: every one of its `21`
pairs has exactly one common dominator. -/
theorem Z1_P7 : Z1 P7 2 = 21 := by decide

/-- `f(3) = 19`, and Paley-19 is extremal for `S_3`. -/
theorem Z1_P19 : Z1 P19 3 = 399 := by decide

/-- **(26) has no absolute constant.**  It claims `Z₁ ≤ C·N²/(k²2^k)`, i.e.
`Z₁ · k² · 2^k ≤ C · N²`.
At `k = 2, N = 7`, `Z₁ = 21`:  `C = 7` suffices.
At `k = 3, N = 19`, `Z₁ = 399`: `C = 7` fails, and `C` must be at least `80`. -/
theorem C_must_grow :
    (21 * 16 ≤ 7 * 49) ∧ ¬ (399 * 72 ≤ 7 * 361) ∧ (399 * 72 ≤ 80 * 361) := by decide

/-- The gap between (25) and (26) is the factor `C(N,k)/N`, which is not a
normalization: it is `51` at `N=19, k=3` and `11440` at `N=67, k=4`. -/
theorem normalization_gap :
    Nat.choose 19 3 = 969 ∧ 969 = 51 * 19 ∧ Nat.choose 67 4 = 766480 := by decide

end JSpaceShot18

#print axioms JSpaceShot18.card_gt_of_HasS
#print axioms JSpaceShot18.deletion_gives_unique_dominator
#print axioms JSpaceShot18.Z1_P7
#print axioms JSpaceShot18.Z1_P19
#print axioms JSpaceShot18.normalization_gap
#print axioms JSpaceShot18.C_must_grow
