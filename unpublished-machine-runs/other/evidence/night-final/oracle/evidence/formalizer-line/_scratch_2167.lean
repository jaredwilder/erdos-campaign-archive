import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def TriangleFree (G : SimpleGraph ℕ) : Prop :=
  ¬ ∃ f : Fin 3 → ℕ,
    Function.Injective f ∧
      ∀ x y : Fin 3, x ≠ y → G.Adj (f x) (f y)

def InfiniteChromatic (G : SimpleGraph ℕ) : Prop :=
  ∀ k : ℕ, ¬ ∃ c : ℕ → Fin k, ∀ ⦃u v : ℕ⦄, G.Adj u v → c u ≠ c v

def ContainsEveryFiniteTree (G : SimpleGraph ℕ) : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
    T.IsTree →
      ∃ f : Fin n → ℕ,
        Function.Injective f ∧
          ∀ x y : Fin n, T.Adj x y ↔ G.Adj (f x) (f y)

def BGraph (α : Type) :=
  α → α → Bool

def BInducedCopy {n m : ℕ} (G : BGraph (Fin n)) (T : BGraph (Fin m)) : Prop :=
  ∃ f : Fin m → Fin n,
    Function.Injective f ∧
      ∀ x y : Fin m,
        (T x y = true) ↔ (G (f x) (f y) = true)

def oneEmpty : BGraph (Fin 1) :=
  fun _ _ => false

theorem witness_pos :
    BInducedCopy oneEmpty (fun _ _ : Fin 1 => false) := by
  refine ⟨id, Function.injective_id, ?_⟩
  intro x y
  simp [oneEmpty]

theorem witness_neg :
    ¬ BInducedCopy oneEmpty (fun _ _ : Fin 2 => false) := by
  rintro ⟨f, hf, _⟩
  have heq : (0 : Fin 2) = 1 := hf (Subsingleton.elim (f 0) (f 1))
  have hne : (0 : Fin 2) ≠ 1 := by decide
  exact hne heq

theorem erdos_738 :
    ∀ G : SimpleGraph ℕ,
      InfiniteChromatic G →
        TriangleFree G →
          ContainsEveryFiniteTree G := by
  sorry

end