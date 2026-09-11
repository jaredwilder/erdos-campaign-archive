import Mathlib

/-!
Erdős 949 — minimality of the multiplier set `{1,2,3,4,5}` (campaign erdos949-extend, 2026-09-05).

The sealed `erdos949_universal` says: every sum-free `S ⊆ ℝ` has some `q ∈ {1,…,5}` with
`q ∉ S ∧ 2q ∉ S`.  `erdos949_five_sharp` says `5` is needed (the value cannot be lowered to `4`).
This file proves the stronger structural fact that the *whole* multiplier set `{1,2,3,4,5}` is
minimal: NO element can be dropped.

`erdos949_multiplier_minimal` : for every `q₀ ∈ {1,…,5}` there is a sum-free `S ⊆ ℝ` whose ONLY
good multiplier in `{1,…,5}` is `q₀` (i.e. `q₀` is good, and any good `q ≤ 5` equals `q₀`).
Consequently, deleting `q₀` from `{1,…,5}` produces a set that fails the universal theorem for this
`S`.  Explicit sum-free witnesses (found by exhaustive search over sum-free `S ⊆ {1..10}`):

  q₀ = 1 : {4,5,6}      q₀ = 2 : {1,6,8,10}     q₀ = 3 : {2,5,8}
  q₀ = 4 : {2,6,10}     q₀ = 5 : {2,3,8}
-/

set_option autoImplicit false

/-- **Minimality of the multiplier set `{1,2,3,4,5}`.**  For each `q₀ ∈ {1,…,5}` there is a
sum-free `S ⊆ ℝ` for which `q₀` is good (`q₀ ∉ S ∧ 2q₀ ∉ S`) and yet `q₀` is the *only* good
multiplier in `{1,…,5}`.  Hence no element of `{1,…,5}` is redundant in `erdos949_universal`. -/
theorem erdos949_multiplier_minimal :
    ∀ q₀ : ℕ, 1 ≤ q₀ → q₀ ≤ 5 →
      ∃ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) ∧
        (((q₀ : ℕ) : ℝ) ∉ S ∧ ((2 * q₀ : ℕ) : ℝ) ∉ S) ∧
        (∀ q : ℕ, 1 ≤ q → q ≤ 5 → ((q : ℕ) : ℝ) ∉ S → ((2 * q : ℕ) : ℝ) ∉ S → q = q₀) := by
  intro q₀ h1 h5
  interval_cases q₀
  · -- q₀ = 1, witness {4,5,6}
    refine ⟨{4, 5, 6}, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hab
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        rcases hab with h | h | h <;> norm_num at h
    · constructor <;> norm_num [Set.mem_insert_iff, Set.mem_singleton_iff]
    · intro q hq1 hq5 hq h2q
      interval_cases q <;>
        first
        | rfl
        | (exfalso; revert hq h2q; norm_num [Set.mem_insert_iff, Set.mem_singleton_iff])
  · -- q₀ = 2, witness {1,6,8,10}
    refine ⟨{1, 6, 8, 10}, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hab
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
        rcases hab with h | h | h | h <;> norm_num at h
    · constructor <;> norm_num [Set.mem_insert_iff, Set.mem_singleton_iff]
    · intro q hq1 hq5 hq h2q
      interval_cases q <;>
        first
        | rfl
        | (exfalso; revert hq h2q; norm_num [Set.mem_insert_iff, Set.mem_singleton_iff])
  · -- q₀ = 3, witness {2,5,8}
    refine ⟨{2, 5, 8}, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hab
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        rcases hab with h | h | h <;> norm_num at h
    · constructor <;> norm_num [Set.mem_insert_iff, Set.mem_singleton_iff]
    · intro q hq1 hq5 hq h2q
      interval_cases q <;>
        first
        | rfl
        | (exfalso; revert hq h2q; norm_num [Set.mem_insert_iff, Set.mem_singleton_iff])
  · -- q₀ = 4, witness {2,6,10}
    refine ⟨{2, 6, 10}, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hab
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        rcases hab with h | h | h <;> norm_num at h
    · constructor <;> norm_num [Set.mem_insert_iff, Set.mem_singleton_iff]
    · intro q hq1 hq5 hq h2q
      interval_cases q <;>
        first
        | rfl
        | (exfalso; revert hq h2q; norm_num [Set.mem_insert_iff, Set.mem_singleton_iff])
  · -- q₀ = 5, witness {2,3,8}
    refine ⟨{2, 3, 8}, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hab
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        rcases hab with h | h | h <;> norm_num at h
    · constructor <;> norm_num [Set.mem_insert_iff, Set.mem_singleton_iff]
    · intro q hq1 hq5 hq h2q
      interval_cases q <;>
        first
        | rfl
        | (exfalso; revert hq h2q; norm_num [Set.mem_insert_iff, Set.mem_singleton_iff])

#print axioms erdos949_multiplier_minimal
