import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

structure FiniteGraph (n : ℕ) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ v, adj v v = false

def validAdjacency (n : ℕ) (a : Fin n → Fin n → Bool) : Prop :=
  (∀ u v, a u v = a v u) ∧ (∀ v, a v v = false)

def edgeCount {n : ℕ} (a : Fin n → Fin n → Bool) : ℕ :=
  (Finset.univ.sum (fun u =>
    Finset.univ.sum (fun v => if a u v = true then 1 else 0))) / 2

def containsGraph {m n : ℕ} (H : FiniteGraph m)
    (a : Fin n → Fin n → Bool) : Prop :=
  ∃ f : Fin m → Fin n,
    Function.Injective f ∧
      ∀ u v, H.adj u v = true → a (f u) (f v) = true

def isCandidate {m n : ℕ} (H : FiniteGraph m)
    (a : Fin n → Fin n → Bool) : Prop :=
  validAdjacency n a ∧ ¬ containsGraph H a

noncomputable def candidates {m : ℕ} (H : FiniteGraph m) (n : ℕ) :
    Finset (Fin n → Fin n → Bool) := by
  classical
  exact Finset.univ.filter (fun a => decide (isCandidate H a))

noncomputable def extremalNumber {m : ℕ} (H : FiniteGraph m) (n : ℕ) : ℕ :=
  (candidates H n).sup edgeCount

def degreeWithin {m : ℕ} (H : FiniteGraph m)
    (S : Finset (Fin m)) (v : Fin m) : ℕ :=
  (S.filter (fun w => H.adj v w = true)).card

def rDegenerate {m : ℕ} (H : FiniteGraph m) (r : ℕ) : Prop :=
  ∀ S : Finset (Fin m), S.Nonempty →
    ∃ v, v ∈ S ∧ degreeWithin H S v ≤ r

def bipartite {m : ℕ} (H : FiniteGraph m) : Prop :=
  ∃ c : Fin m → Bool,
    ∀ u v, H.adj u v = true → c u ≠ c v

theorem erdos_simonovits_conjecture
    {m : ℕ} (H : FiniteGraph m) (r : ℕ) (hr : 0 < r)
    (hbip : bipartite H) (hdeg : rDegenerate H r) :
    ∃ C : ℝ, 0 < C ∧
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        (extremalNumber H n : ℝ) ≤
          C * Real.rpow (n : ℝ) ((2 : ℝ) - (1 : ℝ) / (r : ℝ)) := by
  sorry

end
