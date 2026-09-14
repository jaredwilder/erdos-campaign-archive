import Mathlib

/-! # JSPACE SHOT 7 — the NEST lemma, in the kernel. -/

namespace JSpaceShot7

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

/-- `S` induces a tournament with a source. -/
def hasSource (T : Tournament V) (S : Finset V) : Prop :=
  ∃ s ∈ S, ∀ y ∈ S, y ≠ s → T.beats s y

instance decHasSource (T : Tournament V) : DecidablePred (hasSource T) := by
  intro S; unfold hasSource; infer_instance

/-- Every 1-vertex prefix is transitively rooted.  This is the `r = 0` term of NEST,
and it is `1/(0+1) = 1` on its own. -/
theorem hasSource_singleton (T : Tournament V) (v : V) : hasSource T ({v} : Finset V) := by
  refine ⟨v, Finset.mem_singleton_self v, ?_⟩
  intro y hy hne
  exact absurd (Finset.mem_singleton.mp hy) hne

/-- Every 2-vertex prefix is transitively rooted.  This is the `r = 1` term, worth `1/2`. -/
theorem hasSource_pair (T : Tournament V) (a b : V) (hab : a ≠ b) :
    hasSource T ({a, b} : Finset V) := by
  rcases em (T.beats a b) with h | h
  · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
    intro y hy hne
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact absurd rfl hne
    · rw [Finset.mem_singleton] at hy'; subst hy'; exact h
  · have hba : T.beats b a := by
      by_contra hc
      exact h ((T.tot a b hab).mpr hc)
    refine ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self b), ?_⟩
    intro y hy hne
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact hba
    · rw [Finset.mem_singleton] at hy'; subst hy'; exact absurd rfl hne

/-- **NEST IS FALSE.**  For every tournament with at least two vertices, every
permutation, and every `k ≥ 2`, the sum is at least `3/2`, never `≤ 1`.

The `r = 0` prefix is a single vertex, which is always transitively rooted and
already contributes `1/(0+1) = 1`.  The `r = 1` prefix is two vertices, which is
always transitively rooted and contributes another `1/2`. -/
theorem NEST_false (T : Tournament V) (pre : ℕ → Finset V) (a b : V) (hab : a ≠ b)
    (h1 : pre 1 = ({a} : Finset V)) (h2 : pre 2 = ({a, b} : Finset V))
    {k : ℕ} (hk : 2 ≤ k) :
    ¬ (∑ r ∈ Finset.range k,
        (if hasSource T (pre (r + 1)) then (1 : ℚ) / (r + 1) else 0)) ≤ 1 := by
  have hsub : Finset.range 2 ⊆ Finset.range k := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hnn : ∀ i ∈ Finset.range k, i ∉ Finset.range 2 →
      0 ≤ (if hasSource T (pre (i + 1)) then (1 : ℚ) / (i + 1) else 0) := by
    intro i _ _
    split_ifs with h
    · positivity
    · exact le_refl 0
  have hsmall : (∑ r ∈ Finset.range 2,
      (if hasSource T (pre (r + 1)) then (1 : ℚ) / (r + 1) else 0)) = 3 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    rw [if_pos (by rw [show (0:ℕ) + 1 = 1 from rfl, h1]; exact hasSource_singleton T a),
        if_pos (by rw [show (1:ℕ) + 1 = 2 from rfl, h2]; exact hasSource_pair T a b hab)]
    norm_num
  have hle : (3 : ℚ) / 2 ≤ ∑ r ∈ Finset.range k,
      (if hasSource T (pre (r + 1)) then (1 : ℚ) / (r + 1) else 0) := by
    rw [← hsmall]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  intro hcon
  have : (3 : ℚ) / 2 ≤ 1 := le_trans hle hcon
  norm_num at this

/-! ## The smallest witness. -/

/-- Two vertices, `0 → 1`. -/
def T2 : Tournament (Fin 2) where
  beats a b := a.val < b.val
  dec := inferInstance
  irrefl := by decide
  tot := by decide

/-- Prefixes of the identity permutation on `Fin 2`. -/
def pre2 : ℕ → Finset (Fin 2)
  | 0 => ∅
  | 1 => {0}
  | _ => {0, 1}

/-- **Smallest witness: 2 vertices, `k = 2`.**  NEST claims `≤ 1`; the value is `3/2`. -/
theorem NEST_smallest_witness :
    ¬ (∑ r ∈ Finset.range 2,
        (if hasSource T2 (pre2 (r + 1)) then (1 : ℚ) / (r + 1) else 0)) ≤ 1 :=
  NEST_false T2 pre2 0 1 (by decide) rfl rfl (le_refl 2)

/-- The 3-cycle, `a → a+1`: a genuinely non-transitive tournament, same verdict. -/
def C3 : Tournament (Fin 3) where
  beats a b := b = a + 1
  dec := inferInstance
  irrefl := by decide
  tot := by decide

def pre3 : ℕ → Finset (Fin 3)
  | 0 => ∅
  | 1 => {0}
  | 2 => {0, 1}
  | _ => {0, 1, 2}

theorem NEST_false_on_3cycle {k : ℕ} (hk : 2 ≤ k) :
    ¬ (∑ r ∈ Finset.range k,
        (if hasSource C3 (pre3 (r + 1)) then (1 : ℚ) / (r + 1) else 0)) ≤ 1 :=
  NEST_false C3 pre3 0 1 (by decide) rfl rfl hk

end JSpaceShot7

#print axioms JSpaceShot7.hasSource_singleton
#print axioms JSpaceShot7.hasSource_pair
#print axioms JSpaceShot7.NEST_false
#print axioms JSpaceShot7.NEST_smallest_witness
#print axioms JSpaceShot7.NEST_false_on_3cycle
