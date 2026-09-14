/-
  R(5,5) — THE OBSTRUCTION AS A MACHINE-CHECKABLE INTERFACE.

  Emitted by the MSL v2.0 CLOSE campaign on R(5,5) (gauntlet contract
  MSL-GAUNTLET-CONTRACT-R55-2026-09-03), standing demand (11): if the campaign
  ends unresolved, the terminal package states the final obstruction as a
  precise finite statement a stranger could attack with a solver, at best a
  Lean sorry-stub that typechecks.

  NOTHING HERE IS PROVED. `upperObligation` carries `sorry`. Its presence is the
  point: it names, in a kernel-checkable type, exactly the statement this
  campaign could not reach.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image

namespace R55

/-- A 2-colouring of the edges of the complete graph on `Fin n`, as a symmetric
    `Bool`-valued function.  Diagonal values are irrelevant and unconstrained. -/
structure Colouring (n : ℕ) where
  c : Fin n → Fin n → Bool
  symm : ∀ i j, c i j = c j i

/-- `S` is monochromatic of colour `b`. -/
def Mono {n : ℕ} (χ : Colouring n) (S : Finset (Fin n)) (b : Bool) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → χ.c i j = b

instance {n : ℕ} (χ : Colouring n) (S : Finset (Fin n)) (b : Bool) :
    Decidable (Mono χ S b) := by
  unfold Mono; infer_instance

/-- Some 5-set is monochromatic. -/
def HasMonoK5 {n : ℕ} (χ : Colouring n) : Prop :=
  ∃ S ∈ (Finset.univ : Finset (Fin n)).powersetCard 5,
    Mono χ S true ∨ Mono χ S false

instance {n : ℕ} (χ : Colouring n) : Decidable (HasMonoK5 χ) := by
  unfold HasMonoK5; infer_instance

/-- LOWER CERTIFICATE at `n`: a colouring on `n` vertices with no monochromatic
    `K₅`.  Witnessing this gives `R(5,5) > n`.  It is DECIDABLE for a GIVEN `χ`
    — which is exactly what the session's checker decided, outside the kernel. -/
def LowerCert (n : ℕ) : Prop := ∃ χ : Colouring n, ¬ HasMonoK5 χ

/-- UPPER CERTIFICATE at `n`: every colouring on `n` vertices contains a
    monochromatic `K₅`.  This is the half the campaign never reached. -/
def UpperCert (n : ℕ) : Prop := ∀ χ : Colouring n, HasMonoK5 χ

/-- `R(5,5) = N`, in exactly the two-certificate sense the contract demands. -/
def IsR55 (N : ℕ) : Prop := LowerCert (N - 1) ∧ UpperCert N

/-- The upper certificate is upward closed: this direction IS proved, and it is
    why a single `UpperCert N` settles the whole tail above `N`. -/
theorem upperCert_mono {m n : ℕ} (h : m ≤ n) (hm : UpperCert m) : UpperCert n := by
  intro χ
  obtain ⟨S, hS, hmono⟩ :=
    hm { c := fun i j => χ.c ⟨i.1, lt_of_lt_of_le i.2 h⟩ ⟨j.1, lt_of_lt_of_le j.2 h⟩
       , symm := fun i j => χ.symm _ _ }
  refine ⟨S.image (fun i : Fin m => (⟨i.1, lt_of_lt_of_le i.2 h⟩ : Fin n)), ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective]
    · exact (Finset.mem_powersetCard.mp hS).2
    · intro a b hab; simpa [Fin.ext_iff] using hab
  · rcases hmono with h1 | h1
    · exact Or.inl (by
        intro i hi j hj hij
        simp only [Finset.mem_image] at hi hj
        obtain ⟨a, ha, rfl⟩ := hi; obtain ⟨b, hb, rfl⟩ := hj
        exact h1 a ha b hb (fun hc => hij (by simp [hc])))
    · exact Or.inr (by
        intro i hi j hj hij
        simp only [Finset.mem_image] at hi hj
        obtain ⟨a, ha, rfl⟩ := hi; obtain ⟨b, hb, rfl⟩ := hj
        exact h1 a ha b hb (fun hc => hij (by simp [hc])))

/-!
  ⛔ THE OBSTRUCTION.

  The campaign produced definition-verified lower certificates by explicit
  construction.  It produced NO upper certificate at any order, and the derived
  ceiling (`R(5,5) ≤ 70`, Erdős–Szekeres, in-transcript) is far above the
  frontier.  The exact missing statement, for the frontier order `N` the
  campaign reached, is this — and it is what a stranger with a solver should
  attack:
-/

/-- THE FINAL OBSTRUCTION, unproved.  `N` is the order at which the campaign's
    lower ladder stopped plus one.  Every 2-colouring of `K_N` contains a
    monochromatic `K₅`.  The search space is `2 ^ (N.choose 2)` colourings; no
    method in this campaign decides it. -/
theorem upperObligation (N : ℕ) : UpperCert N := by
  sorry

end R55
