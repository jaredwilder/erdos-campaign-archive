import Mathlib

/-! # JSPACE SHOT 8 — the crown certificate, in the kernel. -/

namespace JSpaceShot8

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

theorem mem_Dset {T : Tournament V} {A : Finset V} {v : V} :
    v ∈ Dset T A ↔ ∀ a ∈ A, T.beats v a := by simp [Dset]

def IsDominating (T : Tournament V) (Q : Finset V) : Prop :=
  ∀ v : V, v ∉ Q → ∃ x ∈ Q, T.beats x v

def IsMinimumDominating (T : Tournament V) (M : Finset V) : Prop :=
  IsDominating T M ∧ ∀ Q : Finset V, IsDominating T Q → M.card ≤ Q.card

/-- Shot 8's residual: `R(S) = D(M \ S)`. -/
def Rset (T : Tournament V) (M S : Finset V) : Finset V := Dset T (M \ S)

/-! ## (2) — TRUE.  `γ(T[R(S)]) ≥ |S|`. -/

/-- **Equation (2) of Shot 8.**  If `M` is a minimum dominating set, `S ⊆ M`, and `Q`
dominates `R(S)` from inside, then `|S| ≤ |Q|`. -/
theorem residual_domination_lower {T : Tournament V} {M : Finset V}
    (hmin : IsMinimumDominating T M) (S : Finset V) (hS : S ⊆ M) (Q : Finset V)
    (hdom : ∀ v ∈ Rset T M S, v ∉ Q → ∃ q ∈ Q, T.beats q v) :
    S.card ≤ Q.card := by
  have hdomU : IsDominating T ((M \ S) ∪ Q) := by
    intro w hw
    rw [Finset.mem_union] at hw
    push_neg at hw
    obtain ⟨hwM, hwQ⟩ := hw
    by_cases hex : ∃ x ∈ M \ S, T.beats x w
    · obtain ⟨x, hx, hxw⟩ := hex
      exact ⟨x, Finset.mem_union_left _ hx, hxw⟩
    · push_neg at hex
      have hwR : w ∈ Rset T M S := by
        refine mem_Dset.mpr (fun x hx => ?_)
        have hne : w ≠ x := fun h => hwM (h ▸ hx)
        by_contra hc
        exact hex x hx ((T.tot x w (Ne.symm hne)).mpr hc)
      obtain ⟨q, hq, hqw⟩ := hdom w hwR hwQ
      exact ⟨q, Finset.mem_union_right _ hq, hqw⟩
  have hcard : M.card ≤ ((M \ S) ∪ Q).card := hmin.2 _ hdomU
  have h1 : ((M \ S) ∪ Q).card ≤ (M \ S).card + Q.card := Finset.card_union_le _ _
  have h2 : (M \ S).card + S.card = M.card := Finset.card_sdiff_add_card_eq_card hS
  have h3 : S.card ≤ M.card := Finset.card_le_card hS
  omega

/-! ## The crown certificate states. -/

/-- A certificate state for `S` is an oriented pair drawn from the residual `R(S)`. -/
def certificateStates (T : Tournament V) (M S : Finset V) : Finset (V × V) :=
  ((Rset T M S) ×ˢ (Rset T M S)).filter (fun p => T.beats p.1 p.2)

theorem sdiff_erase_eq {M : Finset V} {x : V} (hx : x ∈ M) : M \ M.erase x = {x} := by
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton, not_and]
  constructor
  · rintro ⟨hyM, h⟩
    by_contra hne
    exact (h hne) hyM
  · rintro rfl
    exact ⟨hx, fun h => absurd rfl h⟩

/-- At `s = m-1` the residual is exactly the in-neighbourhood: `R(M \ {x}) = D({x})`. -/
theorem Rset_erase {T : Tournament V} {M : Finset V} {x : V} (hx : x ∈ M) :
    Rset T M (M.erase x) = Dset T {x} := by
  unfold Rset
  rw [sdiff_erase_eq hx]

/-- **`crown_states_disjoint` IS FALSE.**  Two distinct common in-neighbours of `x₁`
and `x₂` produce one oriented pair that is a certificate state for BOTH `M \ {x₁}`
and `M \ {x₂}`.  At `s = m-1` the residuals are in-neighbourhoods, and those overlap. -/
theorem crown_states_not_disjoint {T : Tournament V} {M : Finset V} {x₁ x₂ a b : V}
    (h₁ : x₁ ∈ M) (h₂ : x₂ ∈ M) (hab : a ≠ b)
    (ha₁ : a ∈ Dset T {x₁}) (ha₂ : a ∈ Dset T {x₂})
    (hb₁ : b ∈ Dset T {x₁}) (hb₂ : b ∈ Dset T {x₂}) :
    ¬ Disjoint (certificateStates T M (M.erase x₁)) (certificateStates T M (M.erase x₂)) := by
  rcases em (T.beats a b) with hab1 | hab1
  · intro hd
    have hmem : ∀ x : V, x ∈ M → x = x₁ ∨ x = x₂ →
        (a, b) ∈ certificateStates T M (M.erase x) := by
      rintro x hx (rfl | rfl)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨(Rset_erase h₁).symm ▸ ha₁, (Rset_erase h₁).symm ▸ hb₁⟩, hab1⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨(Rset_erase h₂).symm ▸ ha₂, (Rset_erase h₂).symm ▸ hb₂⟩, hab1⟩
    exact (Finset.disjoint_left.mp hd (hmem x₁ h₁ (Or.inl rfl))) (hmem x₂ h₂ (Or.inr rfl))
  · have hba : T.beats b a := by
      by_contra hc
      exact hab1 ((T.tot a b hab).mpr hc)
    intro hd
    have hm1 : (b, a) ∈ certificateStates T M (M.erase x₁) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(Rset_erase h₁).symm ▸ hb₁, (Rset_erase h₁).symm ▸ ha₁⟩, hba⟩
    have hm2 : (b, a) ∈ certificateStates T M (M.erase x₂) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(Rset_erase h₂).symm ▸ hb₂, (Rset_erase h₂).symm ▸ ha₂⟩, hba⟩
    exact (Finset.disjoint_left.mp hd hm1) hm2

/-! ## A concrete tournament where the hypothesis holds. -/

/-- Paley-7 on `{0,...,6}`, plus a vertex `7` that beats `{0,1,2}` and is beaten by
`{3,4,5,6}`. -/
def T8 : Tournament (Fin 8) where
  beats a b :=
    if a.val = 7 then b.val < 3
    else if b.val = 7 then 3 ≤ a.val ∧ a.val < 7
    else ((b.val + 7 - a.val) % 7 = 1 ∨ (b.val + 7 - a.val) % 7 = 2 ∨
          (b.val + 7 - a.val) % 7 = 4)
  dec := inferInstance
  irrefl := by decide
  tot := by decide

set_option maxRecDepth 1000000 in
/-- `M = {0,1,4}` is a minimum dominating set of `T8`, so `m = γ(T8) = 3`. -/
theorem T8_min : IsMinimumDominating T8 ({0, 1, 4} : Finset (Fin 8)) := by
  constructor
  · show ∀ v : Fin 8, v ∉ ({0,1,4} : Finset (Fin 8)) → ∃ x ∈ ({0,1,4} : Finset (Fin 8)),
      T8.beats x v
    decide
  · show ∀ Q : Finset (Fin 8),
      (∀ v : Fin 8, v ∉ Q → ∃ x ∈ Q, T8.beats x v) → ({0,1,4} : Finset (Fin 8)).card ≤ Q.card
    decide

/-- `6` and `7` both beat `0` and both beat `1`. -/
theorem T8_common :
    (6 : Fin 8) ∈ Dset T8 {0} ∧ (6 : Fin 8) ∈ Dset T8 {1} ∧
    (7 : Fin 8) ∈ Dset T8 {0} ∧ (7 : Fin 8) ∈ Dset T8 {1} := by decide

/-- **The concrete refutation.**  `T8` has minimum dominating set `M = {0,1,4}`, and the
certificate states of `M \ {0}` and `M \ {1}` are NOT disjoint. -/
theorem crown_states_disjoint_fails :
    IsMinimumDominating T8 ({0, 1, 4} : Finset (Fin 8)) ∧
    ¬ Disjoint
        (certificateStates T8 ({0,1,4} : Finset (Fin 8)) (({0,1,4} : Finset (Fin 8)).erase 0))
        (certificateStates T8 ({0,1,4} : Finset (Fin 8)) (({0,1,4} : Finset (Fin 8)).erase 1)) := by
  refine ⟨T8_min, ?_⟩
  obtain ⟨h60, h61, h70, h71⟩ := T8_common
  exact crown_states_not_disjoint (by decide) (by decide) (by decide) h60 h61 h70 h71

end JSpaceShot8

#print axioms JSpaceShot8.residual_domination_lower
#print axioms JSpaceShot8.Rset_erase
#print axioms JSpaceShot8.crown_states_not_disjoint
#print axioms JSpaceShot8.T8_min
#print axioms JSpaceShot8.crown_states_disjoint_fails
