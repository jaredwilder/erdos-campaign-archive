import Mathlib

/-! # JSPACE SHOT 12 — the nested cut, in the kernel. -/

namespace JSpaceShot12

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

/-! ## `unique_directed_cut`. -/

/-- **As stated, it is FALSE**: nothing forces `B₁` and `B₂` to lie inside `C`, so with
`C = ∅` both hypotheses are vacuous. -/
def T2 : Tournament (Fin 2) where
  beats a b := a.val < b.val
  dec := inferInstance
  irrefl := by decide
  tot := by decide

theorem unique_directed_cut_false_as_stated :
    ¬ (∀ (C B₁ B₂ : Finset (Fin 2)), B₁.card = B₂.card →
        (∀ x ∈ B₁, ∀ y ∈ C \ B₁, T2.beats x y) →
        (∀ x ∈ B₂, ∀ y ∈ C \ B₂, T2.beats x y) → B₁ = B₂) := by
  intro h
  have hcon := h ∅ {0} {1} (by decide) (by decide) (by decide)
  revert hcon
  decide

/-- **With `B₁, B₂ ⊆ C` added, it is TRUE.**  Your argument goes through unchanged. -/
theorem unique_directed_cut {T : Tournament V} {C B₁ B₂ : Finset V}
    (hB₁ : B₁ ⊆ C) (hB₂ : B₂ ⊆ C) (hcard : B₁.card = B₂.card)
    (h₁ : ∀ x ∈ B₁, ∀ y ∈ C \ B₁, T.beats x y)
    (h₂ : ∀ x ∈ B₂, ∀ y ∈ C \ B₂, T.beats x y) :
    B₁ = B₂ := by
  by_contra hne
  have hd₁ : (B₁ \ B₂).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc
    exact hne (Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp hc)
      (le_of_eq hcard.symm))
  have hd₂ : (B₂ \ B₁).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc
    exact hne (Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp hc)
      (le_of_eq hcard)).symm
  obtain ⟨x, hx⟩ := hd₁
  obtain ⟨y, hy⟩ := hd₂
  rw [Finset.mem_sdiff] at hx hy
  have hxy : T.beats x y :=
    h₁ x hx.1 y (Finset.mem_sdiff.mpr ⟨hB₂ hy.1, hy.2⟩)
  have hyx : T.beats y x :=
    h₂ y hy.1 x (Finset.mem_sdiff.mpr ⟨hB₁ hx.1, hx.2⟩)
  have hne' : x ≠ y := fun hc => hy.2 (hc ▸ hx.1)
  exact ((T.tot x y hne').mp hxy) hyx

/-! ## `nested_cut_bound`.

Shot 12 asserts, for `k ≥ 6`,

    C(N,2) · C(k·2^(k-3) - 1, 2) · C((k-2)·2^(k-5) - 1, k-4)  ≤  C(N, k+2)

and then claims the second Szekeres factor "contributes precisely another asymptotic
factor `k`", giving `N ≥ c k² 2^k`.

It does not.  Below, the inequality is checked at `N` equal to the **Szekeres bound
itself**, `f(k) ≥ (k+2)2^(k-1) - 1`.  It holds there.  An inequality already satisfied
at the Szekeres value cannot force anything past the Szekeres value, in particular not
`k² 2^k`. -/

def binom (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

theorem binom_eq (n k : ℕ) : Nat.choose n k = binom n k :=
  Nat.choose_eq_descFactorial_div_factorial n k

/-- `k = 6`:  Szekeres gives `f(6) ≥ 255`.  The nested-cut inequality holds at `N = 255`,
while `k²2^k = 2304`. -/
theorem nested_holds_at_szekeres_k6 :
    Nat.choose 255 2 * Nat.choose 47 2 * Nat.choose 7 2 ≤ Nat.choose 255 8 := by
  rw [binom_eq, binom_eq, binom_eq, binom_eq]
  decide

/-- `k = 10`:  Szekeres gives `f(10) ≥ 6143`.  The inequality holds at `N = 6143`,
while `k²2^k = 102400`. -/
theorem nested_holds_at_szekeres_k10 :
    Nat.choose 6143 2 * Nat.choose 1279 2 * Nat.choose 255 6 ≤ Nat.choose 6143 12 := by
  rw [binom_eq, binom_eq, binom_eq, binom_eq]
  decide

/-- `k = 14`:  Szekeres gives `f(14) ≥ 131071`.  The inequality holds at `N = 131071`,
while `k²2^k = 3211264`. -/
theorem nested_holds_at_szekeres_k14 :
    Nat.choose 131071 2 * Nat.choose 28671 2 * Nat.choose 6143 10
      ≤ Nat.choose 131071 16 := by
  rw [binom_eq, binom_eq, binom_eq, binom_eq]
  decide

/-- And it already holds far BELOW the Szekeres value: at `k = 10` the inequality is
satisfied at `N = 512`, an order of magnitude under `f(10) ≥ 6143` and two orders under
`k²2^k = 102400`. -/
theorem nested_holds_at_512_k10 :
    Nat.choose 512 2 * Nat.choose 1279 2 * Nat.choose 255 6 ≤ Nat.choose 512 12 := by
  rw [binom_eq, binom_eq, binom_eq, binom_eq]
  decide

/-- The comparison, so the numbers are on the record. -/
theorem the_gap :
    (6143 : ℕ) < 102400 ∧ (512 : ℕ) < 6143 ∧ (131071 : ℕ) < 3211264 := by decide

end JSpaceShot12

#print axioms JSpaceShot12.unique_directed_cut_false_as_stated
#print axioms JSpaceShot12.unique_directed_cut
#print axioms JSpaceShot12.nested_holds_at_szekeres_k6
#print axioms JSpaceShot12.nested_holds_at_szekeres_k10
#print axioms JSpaceShot12.nested_holds_at_szekeres_k14
#print axioms JSpaceShot12.nested_holds_at_512_k10
