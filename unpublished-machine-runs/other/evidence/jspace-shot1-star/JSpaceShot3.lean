import Mathlib

/-!
# JSPACE SHOT 3 — adjudication in the kernel.

Fired in the order requested: (16), then (25), then (26).
Reuses the Shot-2 setting: `D(A) = {v : v → a for all a ∈ A}`,
`Schutte T k` (= `γ(T) > k`) : every `A` with `|A| ≤ k` has `D(A) ≠ ∅`.

SURVIVING:  (1) `noncollapse`, (2) `Mlev_ge`, (5) `Mlev_eq`, (25) `residual_compose`.
DEAD:       (16) as stated, (23), (26).
-/

namespace JSpaceShot3

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

def Schutte (T : Tournament V) (k : ℕ) : Prop :=
  ∀ A : Finset V, A.card ≤ k → (Dset T A).Nonempty

/-- Out-neighbourhood and out-degree. -/
def Nout (T : Tournament V) (v : V) : Finset V := univ.filter (fun u => T.beats v u)
def outdeg (T : Tournament V) (v : V) : ℕ := (Nout T v).card

/-! ## SURVIVOR: equation (1), carried over from Shot 2. -/

theorem noncollapse {T : Tournament V} {k : ℕ} (h : Schutte T k)
    (A : Finset V) (hA : A.card ≤ k) : k + 1 ≤ A.card + (Dset T A).card := by
  by_contra hc
  push_neg at hc
  have hB : (A ∪ Dset T A).card ≤ k := by
    have := Finset.card_union_le A (Dset T A); omega
  obtain ⟨v, hv⟩ := h _ hB
  have hv2 : ∀ b ∈ A ∪ Dset T A, T.beats v b := (mem_filter.mp hv).2
  have hvA : v ∈ Dset T A := by
    refine mem_filter.mpr ⟨mem_univ _, fun a ha => hv2 a (Finset.mem_union_left _ ha)⟩
  exact T.irrefl v (hv2 v (Finset.mem_union_right _ hvA))

/-! ## FIRE 2 (fired first, it is the cheap one): equation (25). -/

/-- The general composition law: `D(A ∪ B) = D(A) ∩ D(B)`. -/
theorem Dset_union (T : Tournament V) (A B : Finset V) :
    Dset T (A ∪ B) = Dset T A ∩ Dset T B := by
  ext v
  simp only [Dset, mem_filter, mem_univ, true_and, mem_inter, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun a ha => h a (Or.inl ha), fun b hb => h b (Or.inr hb)⟩
  · rintro ⟨h1, h2⟩ a (ha | ha)
    · exact h1 a ha
    · exact h2 a ha

/-- **Equation (25). TRUE.**  Taking `D` inside the residual tournament on `D(A)`
returns exactly `D_T(A ∪ B)`.  No disjointness hypothesis is needed. -/
theorem residual_compose (T : Tournament V) (A B : Finset V) :
    (Dset T A).filter (fun v => ∀ b ∈ B, T.beats v b) = Dset T (A ∪ B) := by
  rw [Dset_union]
  ext v
  simp only [Dset, mem_filter, mem_univ, true_and, mem_inter]

/-! ## SURVIVORS: equations (2) and (5). -/

/-- `M_r = Σ_{|A|=r} |D(A)|`. -/
def Mlev (T : Tournament V) (r : ℕ) : ℕ :=
  ∑ A ∈ powersetCard r (univ : Finset V), (Dset T A).card

/-- **Equation (2). TRUE.**  `M_r ≥ (k-r+1)·C(N,r)`, stated without truncated subtraction. -/
theorem Mlev_ge {T : Tournament V} {k r : ℕ} (h : Schutte T k) (hr : r ≤ k) :
    (k + 1 - r) * (Nat.choose (Fintype.card V) r) ≤ Mlev T r := by
  have key : ∀ A ∈ powersetCard r (univ : Finset V), k + 1 - r ≤ (Dset T A).card := by
    intro A hA
    have hAc : A.card = r := (mem_powersetCard.mp hA).2
    have := noncollapse h A (by omega)
    omega
  calc (k + 1 - r) * (Nat.choose (Fintype.card V) r)
      = ∑ _A ∈ powersetCard r (univ : Finset V), (k + 1 - r) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
            smul_eq_mul, Nat.mul_comm]
    _ ≤ Mlev T r := Finset.sum_le_sum key

/-- **Equation (5). TRUE.**  The double count `M_r = Σ_v C(d⁺(v), r)`. -/
theorem Mlev_eq (T : Tournament V) (r : ℕ) :
    Mlev T r = ∑ v : V, Nat.choose (outdeg T v) r := by
  have step : ∀ v : V,
      (powersetCard r (univ : Finset V)).filter (fun A => ∀ a ∈ A, T.beats v a)
        = powersetCard r (Nout T v) := by
    intro v
    ext A
    simp only [mem_filter, mem_powersetCard, Nout, Finset.subset_iff, mem_filter, mem_univ,
      true_and]
    tauto
  unfold Mlev Dset
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, step v, Finset.card_powersetCard,
      smul_eq_mul, Nat.mul_one]
  rfl

/-! ## FIRE 1: equation (16).  `Σ_v p_v^j ≤ 2N/(j+1)` with `p_v = d⁺(v)/(N-1)`. -/

def Pmom (T : Tournament V) (j : ℕ) : ℚ :=
  ∑ v : V, ((outdeg T v : ℚ) / ((Fintype.card V : ℚ) - 1)) ^ j

/-- Transitive tournament on 3 vertices: `a → b` iff `a < b`. -/
def T3 : Tournament (Fin 3) where
  beats a b := a.val < b.val
  dec := inferInstance
  irrefl := by decide
  tot := by decide

/-- **Equation (16) is FALSE as stated.**  `j` is not tied to `N` anywhere in Shot 3,
and a vertex with `p_v = 1` contributes `1` to the left side for every `j`,
while the right side `2N/(j+1)` tends to `0`.
Witness: transitive `T3`, `j = 5`.  Left side `33/32`, right side `1`. -/
theorem eq16_false_as_stated : ¬ (Pmom T3 5 ≤ (2 * 3 : ℚ) / (5 + 1)) := by
  have h0 : outdeg T3 0 = 2 := by decide
  have h1 : outdeg T3 1 = 1 := by decide
  have h2 : outdeg T3 2 = 0 := by decide
  simp only [Pmom, Fin.sum_univ_three, h0, h1, h2]
  norm_num

/-! ## FIRE 3: the load-bearing collapse, equations (23) and (26). -/

/-- Paley / quadratic-residue tournament on 7 vertices: `a → b` iff `b - a ∈ {1,2,4}`. -/
def P7 : Tournament (Fin 7) where
  beats a b := (b - a) = 1 ∨ (b - a) = 2 ∨ (b - a) = 4
  dec := inferInstance
  irrefl := by decide
  tot := by decide

set_option maxRecDepth 100000 in
/-- `P7` satisfies the hypothesis of Shot 3 at `k = 2`, i.e. `γ(P7) > 2`. -/
theorem P7_schutte : Schutte P7 2 := by
  show ∀ A : Finset (Fin 7), A.card ≤ 2 → (Dset P7 A).Nonempty
  decide

/-- **Equation (23) is FALSE.**  At `k = 2` it demands
`N ≥ 2²·(2/1 + 1/2) = 10`, but `P7` has `γ > 2` with `N = 7`. -/
theorem eq23_false :
    Schutte P7 2 ∧
    (Fintype.card (Fin 7) : ℚ) < 2 ^ 2 * (∑ r ∈ range 2, ((2 - r : ℚ) / (r + 1))) := by
  refine ⟨P7_schutte, ?_⟩
  simp [Finset.sum_range_succ]
  norm_num

/-- **Equation (26) is FALSE.**  At `k = 2` the double sum is
`2/1 + 1/2 + 1/2 = 3`, so it demands `N ≥ 2²·3 = 12`, but `N = 7`. -/
theorem eq26_false :
    Schutte P7 2 ∧
    (Fintype.card (Fin 7) : ℚ) <
      2 ^ 2 * (∑ i ∈ range 2, ∑ j ∈ range 2,
        (if i + j < 2 then ((2 - i - j : ℚ) / ((i + 1) * (j + 1))) else 0)) := by
  refine ⟨P7_schutte, ?_⟩
  simp [Finset.sum_range_succ]
  norm_num

end JSpaceShot3

#print axioms JSpaceShot3.residual_compose
#print axioms JSpaceShot3.Mlev_eq
#print axioms JSpaceShot3.Mlev_ge
#print axioms JSpaceShot3.eq16_false_as_stated
#print axioms JSpaceShot3.eq23_false
#print axioms JSpaceShot3.eq26_false
