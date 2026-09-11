/-
Erdos Problem 52 -- the dilation normalisation, kernel-checked.

Campaign : erdos52-close-2026-09-05
Companion to Erdos52Frag.lean; self-contained, no sorry.

Content: the frozen target's three observables (|A|, |A+A|, |AA|) are simultaneously
invariant under A |-> lambda * A for every nonzero integer lambda. Consequence: the
target may be attacked over any dilation-normalised family (e.g. gcd(A) = 1) with no
loss, and no route claiming a dilation normalisation owes a bridge.
-/
import Mathlib

open scoped Pointwise

namespace Erdos52Dil

/-- Dilation of a finite integer set by `c`. -/
def dil (c : ℤ) (A : Finset ℤ) : Finset ℤ := A.image (fun x => c * x)

theorem card_dil {c : ℤ} (hc : c ≠ 0) (A : Finset ℤ) : (dil c A).card = A.card := by
  have hinj : Function.Injective (fun x : ℤ => c * x) := fun x y h => by
    simpa using mul_left_cancel₀ hc h
  rw [dil, Finset.card_image_of_injective _ hinj]

theorem dil_add (c : ℤ) (A : Finset ℤ) : dil c A + dil c A = dil c (A + A) := by
  ext x
  simp only [dil, Finset.mem_add, Finset.mem_image]
  constructor
  · rintro ⟨u, ⟨a, ha, rfl⟩, v, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨c * a, ⟨a, ha, rfl⟩, c * b, ⟨b, hb, rfl⟩, by ring⟩

theorem dil_mul (c : ℤ) (A : Finset ℤ) : dil c A * dil c A = dil (c * c) (A * A) := by
  ext x
  simp only [dil, Finset.mem_mul, Finset.mem_image]
  constructor
  · rintro ⟨u, ⟨a, ha, rfl⟩, v, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨c * a, ⟨a, ha, rfl⟩, c * b, ⟨b, hb, rfl⟩, by ring⟩

/-- The three observables of the frozen target are simultaneously dilation invariant. -/
theorem dilation_invariant {c : ℤ} (hc : c ≠ 0) (A : Finset ℤ) :
    (dil c A).card = A.card ∧
    (dil c A + dil c A).card = (A + A).card ∧
    (dil c A * dil c A).card = (A * A).card := by
  refine ⟨card_dil hc A, ?_, ?_⟩
  · rw [dil_add, card_dil hc]
  · rw [dil_mul, card_dil (mul_ne_zero hc hc)]

/-- The frozen inequality transports along any nonzero dilation, in both directions. -/
theorem inequality_dilation_invariant {c : ℤ} (hc : c ≠ 0) (C ε : ℝ) (A : Finset ℤ) :
    ((max (dil c A + dil c A).card (dil c A * dil c A).card : ℝ)
        ≥ C * ((dil c A).card : ℝ) ^ (2 - ε))
      ↔ ((max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)) := by
  obtain ⟨h1, h2, h3⟩ := dilation_invariant hc A
  rw [h1, h2, h3]

end Erdos52Dil

#print axioms Erdos52Dil.card_dil
#print axioms Erdos52Dil.dil_add
#print axioms Erdos52Dil.dil_mul
#print axioms Erdos52Dil.dilation_invariant
#print axioms Erdos52Dil.inequality_dilation_invariant
