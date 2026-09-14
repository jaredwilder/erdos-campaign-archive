import Mathlib

/-! # JSPACE SHOT 16 — the rank bridge (7), in the kernel.

    gram_rank_ge_johnson :
      G PSD,  K ≤ G entrywise,  K ∈ Johnson Bose–Mesner  ⟹  rank K ≤ rank G

`G` is a genuine Gram matrix `X Xᴴ`, exactly as in Shot 16's (5), so `rank G ≤ N`.
`K` is the identity, which is `A₀`, the first relation of the Johnson scheme, hence in
its Bose–Mesner algebra (the algebra is unital and `A₀ = I`).  Every hypothesis holds
and the conclusion fails. -/

namespace JSpaceShot16

open Matrix

/-- `X` is a single column: `N = 1` in Shot 16's notation. -/
def X2 : Matrix (Fin 2) (Fin 1) ℚ := fun _ _ => 1

/-- `G = X Xᴴ`, a Gram matrix of rank at most `1`. -/
def G2 : Matrix (Fin 2) (Fin 2) ℚ := X2 * X2ᴴ

/-- `K = I = A₀` of the Johnson scheme. -/
def K2 : Matrix (Fin 2) (Fin 2) ℚ := 1

/-- `G` is positive semidefinite, being `X Xᴴ`. -/
theorem G2_psd : G2.PosSemidef := posSemidef_self_mul_conjTranspose X2

theorem G2_entries : ∀ i j, G2 i j = 1 := by
  intro i j
  simp [G2, X2, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- `K ≤ G` entrywise. -/
theorem K2_le_G2 : ∀ i j, K2 i j ≤ G2 i j := by
  intro i j
  rw [G2_entries]
  by_cases h : i = j
  · simp [K2, Matrix.one_apply, h]
  · simp [K2, Matrix.one_apply_ne h]

theorem rank_K2 : K2.rank = 2 := by
  simp [K2, Matrix.rank_one]

theorem rank_G2 : G2.rank ≤ 1 := by
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  simpa using Matrix.rank_le_card_width X2

/-- **`gram_rank_ge_johnson` IS FALSE.**  `G` is PSD and a Gram matrix, `K ≤ G`
entrywise, `K` lies in the Johnson Bose–Mesner algebra, and yet
`rank K = 2 > 1 ≥ rank G`. -/
theorem gram_rank_ge_johnson_false :
    G2.PosSemidef ∧ (∀ i j, K2 i j ≤ G2 i j) ∧ ¬ (K2.rank ≤ G2.rank) := by
  refine ⟨G2_psd, K2_le_G2, ?_⟩
  have h1 := rank_K2
  have h2 := rank_G2
  omega

/-- The gap is not bounded either: the same construction on `Fin n` gives
`rank K = n` against `rank G ≤ 1`. -/
def Xn (n : ℕ) : Matrix (Fin n) (Fin 1) ℚ := fun _ _ => 1
def Gn (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := Xn n * (Xn n)ᴴ
def Kn (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := 1

theorem Kn_le_Gn (n : ℕ) : ∀ i j, Kn n i j ≤ Gn n i j := by
  intro i j
  have hg : Gn n i j = 1 := by
    simp [Gn, Xn, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hg]
  by_cases h : i = j
  · simp [Kn, Matrix.one_apply, h]
  · simp [Kn, Matrix.one_apply_ne h]

theorem rank_gap_unbounded (n : ℕ) :
    (Kn n).rank = n ∧ (Gn n).rank ≤ 1 := by
  constructor
  · simp [Kn, Matrix.rank_one]
  · refine le_trans (Matrix.rank_mul_le_left _ _) ?_
    simpa using Matrix.rank_le_card_width (Xn n)

end JSpaceShot16

#print axioms JSpaceShot16.G2_psd
#print axioms JSpaceShot16.K2_le_G2
#print axioms JSpaceShot16.rank_K2
#print axioms JSpaceShot16.rank_G2
#print axioms JSpaceShot16.gram_rank_ge_johnson_false
#print axioms JSpaceShot16.rank_gap_unbounded
