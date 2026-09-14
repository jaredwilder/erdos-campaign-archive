import Mathlib

/-! # JSPACE SHOT 13 — CYC, in the kernel. -/

namespace JSpaceShot13

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

def indeg (T : Tournament V) (v : V) : ℕ := (univ.filter (fun u => T.beats u v)).card
def outdeg (T : Tournament V) (v : V) : ℕ := (univ.filter (fun u => T.beats v u)).card

def Dset (T : Tournament V) (A : Finset V) : Finset V :=
  univ.filter (fun v => ∀ a ∈ A, T.beats v a)

def HasS (T : Tournament V) (k : ℕ) : Prop :=
  ∀ A : Finset V, A.card ≤ k → (Dset T A).Nonempty

/-! ## (1) — TRUE.  The in-neighbourhood inherits `S_{k-1}`. -/

/-- **Equation (1) of Shot 13.**  If `A ⊆ N⁻(x)` and `|A| ≤ k-1`, then `A` has a
dominator lying inside `N⁻(x)`. -/
theorem indeg_inherits {T : Tournament V} {k : ℕ} (h : HasS T k) (x : V)
    (A : Finset V) (hA : ∀ a ∈ A, T.beats a x) (hc : A.card + 1 ≤ k) :
    ∃ v, T.beats v x ∧ ∀ a ∈ A, T.beats v a := by
  have hcard : (insert x A).card ≤ k :=
    le_trans (Finset.card_insert_le _ _) (by omega)
  obtain ⟨v, hv⟩ := h _ hcard
  rw [Dset, Finset.mem_filter] at hv
  exact ⟨v, hv.2 x (Finset.mem_insert_self _ _),
    fun a ha => hv.2 a (Finset.mem_insert_of_mem ha)⟩

/-! ## The degree identity. -/

theorem indeg_add_outdeg (T : Tournament V) (v : V) :
    indeg T v + outdeg T v = Fintype.card V - 1 := by
  have hdisj : Disjoint (univ.filter (fun u => T.beats u v))
      (univ.filter (fun u => T.beats v u)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_filter] at ha hb
    by_cases hav : a = v
    · subst hav; exact T.irrefl a ha.2
    · exact ((T.tot a v hav).mp ha.2) hb.2
  have hunion : (univ.filter (fun u => T.beats u v)) ∪ (univ.filter (fun u => T.beats v u))
      = univ.erase v := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro (ha | ha)
      · intro hc; subst hc; exact T.irrefl a ha
      · intro hc; subst hc; exact T.irrefl a ha
    · intro hav
      by_cases hb : T.beats a v
      · exact Or.inl hb
      · exact Or.inr ((T.tot v a (Ne.symm hav)).mpr hb)
  have := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at this
  exact this.symm ▸ rfl

theorem sum_indeg_eq_sum_outdeg (T : Tournament V) :
    ∑ v : V, indeg T v = ∑ v : V, outdeg T v := by
  simp only [indeg, outdeg, Finset.card_filter]
  exact Finset.sum_comm

theorem two_mul_sum_indeg (T : Tournament V) :
    2 * (∑ v : V, indeg T v) = Fintype.card V * (Fintype.card V - 1) := by
  have h1 : ∑ v : V, (indeg T v + outdeg T v) = Fintype.card V * (Fintype.card V - 1) := by
    rw [Finset.sum_congr rfl (fun v _ => indeg_add_outdeg T v)]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← sum_indeg_eq_sum_outdeg] at h1
  omega

/-! ## CYC. -/

/-- **What the hypothesis of CYC forces.**  If every indegree is at least `m`, then
`2m + 1 ≤ N`.  Minimum indegree can never exceed the average `(N-1)/2`. -/
theorem two_mul_min_indeg_lt {T : Tournament V} {m : ℕ}
    (h : ∀ v : V, m ≤ indeg T v) (hN : 0 < Fintype.card V) :
    2 * m + 1 ≤ Fintype.card V := by
  have hsum : Fintype.card V * m ≤ ∑ v : V, indeg T v := by
    calc Fintype.card V * m = ∑ _v : V, m := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ v : V, indeg T v := Finset.sum_le_sum (fun v _ => h v)
  have h2 := two_mul_sum_indeg T
  have hkey : Fintype.card V * (2 * m) ≤ Fintype.card V * (Fintype.card V - 1) := by
    calc Fintype.card V * (2 * m) = 2 * (Fintype.card V * m) := by ring
      _ ≤ 2 * (∑ v : V, indeg T v) := by omega
      _ = Fintype.card V * (Fintype.card V - 1) := h2
  have := Nat.le_of_mul_le_mul_left hkey hN
  omega

/-- **CYC IS VACUOUS.**  Under its own hypothesis the factor `2m + 1 - N` is `0` in `ℕ`,
so the whole right-hand side is `0`. -/
theorem CYC_rhs_zero {T : Tournament V} {m : ℕ}
    (h : ∀ v : V, m ≤ indeg T v) (hN : 0 < Fintype.card V) :
    m * (Fintype.card V - m) * (2 * m + 1 - Fintype.card V) = 0 := by
  have := two_mul_min_indeg_lt h hN
  have hz : 2 * m + 1 - Fintype.card V = 0 := Nat.sub_eq_zero_of_le this
  rw [hz, Nat.mul_zero]

/-- CYC therefore holds for every tournament and every count whatsoever — it is the
statement `0 ≤ 2·C₃`. -/
theorem CYC_holds_vacuously {T : Tournament V} {m : ℕ}
    (h : ∀ v : V, m ≤ indeg T v) (hN : 0 < Fintype.card V) (cyclicTripleCount : ℕ) :
    m * (Fintype.card V - m) * (2 * m + 1 - Fintype.card V) ≤ 2 * cyclicTripleCount := by
  rw [CYC_rhs_zero h hN]
  exact Nat.zero_le _

end JSpaceShot13

#print axioms JSpaceShot13.indeg_inherits
#print axioms JSpaceShot13.indeg_add_outdeg
#print axioms JSpaceShot13.two_mul_sum_indeg
#print axioms JSpaceShot13.two_mul_min_indeg_lt
#print axioms JSpaceShot13.CYC_rhs_zero
#print axioms JSpaceShot13.CYC_holds_vacuously
