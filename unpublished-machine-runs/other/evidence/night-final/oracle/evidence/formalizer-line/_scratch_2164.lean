import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Formalization of Erdős Problem #876.

The source asks about an infinite increasing sum-free sequence
`a₁ < a₂ < ⋯`, where there are no solutions
`a = b₁ + ⋯ + bᵣ` with `b₁ < ⋯ < bᵣ < a` and all terms in the set.
The recorded resolution mentions bounds involving `n`, `n ^ (1 + o(1))`,
`N`, `N log N`, exponents `1/2`, `3 + o(1)`, and constants `100`, `4`,
and `2`, as well as references [Er75b], [Er77c], [Er98], [Er62c],
[DEM99], [LuSc00], and [790].
-/

/-- A finite set is sum-free in the sense of the problem. -/
def FiniteSumFree (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, ∀ t ∈ s.powerset,
    t.Nonempty →
    (∀ b ∈ t, b < a) →
    t.sum id ≠ a

/-- An increasing sequence whose finite initial segments satisfy the
sum-free condition from the problem. -/
def InfiniteSumFree (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧
    ∀ n : ℕ, ∀ t ∈ (Finset.range (n + 1)).powerset,
      t.Nonempty →
      (∀ i ∈ t, a i < a n) →
      t.sum (fun i => a i) ≠ a n

/-- The proposed gap bound, with the sequence indexed from `0` and the
original positive index `n` retained in the inequality. -/
def HasGapsBelowIndex (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → a (n + 1) - a n < n

/-- A concrete finite sum-free example. -/
theorem witness_pos : FiniteSumFree ({1, 2} : Finset ℕ) := by
  classical
  intro a ha t ht hn hlt
  have hsub : t ⊆ ({1, 2} : Finset ℕ) :=
    Finset.mem_powerset.mp ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · rcases hn with ⟨x, hx⟩
    have hx' := hsub hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    have hxlt : x < 1 := hlt x hx
    rcases hx' with hx' | hx' <;> omega
  · have h1 : 1 ∈ t := by
      rcases hn with ⟨x, hx⟩
      have hx' := hsub hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl
      · exact hx
      · exfalso
        have hxlt : 2 < 2 := hlt 2 hx
        omega
    have ht_eq : t = ({1} : Finset ℕ) := by
      ext x
      constructor
      · intro hx
        have hx' := hsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with rfl | rfl
        · simp
        · exfalso
          have hxlt : 2 < 2 := hlt 2 hx
          omega
      · intro hx
        have hx1 : x = 1 := by simpa using hx
        rw [hx1]
        exact h1
    rw [ht_eq]
    norm_num

/-- A concrete finite set which is not sum-free, since `3 = 1 + 2`. -/
theorem witness_neg : ¬ FiniteSumFree ({1, 2, 3} : Finset ℕ) := by
  intro h
  have hbad : ({1, 2} : Finset ℕ).sum id ≠ 3 :=
    h 3 (by simp) {1, 2} (by simp) (by simp) (by simp)
  norm_num at hbad

/-- The yes/no question in Erdős Problem #876. -/
theorem erdos_876 :
    ∃ a : ℕ → ℕ, InfiniteSumFree a ∧ HasGapsBelowIndex a := by
  sorry

end