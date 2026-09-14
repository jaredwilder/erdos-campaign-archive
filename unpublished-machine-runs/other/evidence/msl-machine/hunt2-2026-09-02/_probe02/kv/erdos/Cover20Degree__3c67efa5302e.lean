import Mathlib

set_option autoImplicit false


/-!
C(13,6,3) covering design, P0 promotion (GPT gold pack rank 6 / A11, audited 2026-09-01;
kernel round 2026-09-02). Raw-only theorem from the MSL court runs (run20 / run23b): in any
family of 20 six-subsets of a 13-point set covering every triple, every point lies in at
least 8 blocks. Proof by double counting: for y ≠ x the pair {x,y} lies in ≥ 3 blocks
(11 third points, ≤ 4 per block), and Σ_{y≠x} r_xy = 5 r_x, so 5 r_x ≥ 36.
The estate holds two verified 21-block coverings; this theorem constrains any 20-block one.
-/


open Finset

/-- A covering: every 3-subset of `Fin 13` lies inside some block. -/
def CoversTriples (B : Finset (Finset (Fin 13))) : Prop :=
  ∀ T : Finset (Fin 13), T.card = 3 → ∃ b ∈ B, T ⊆ b

/-- Pair count: blocks containing both `x` and `y`. -/
theorem cover20_pair_count (B : Finset (Finset (Fin 13)))
    (hsize : ∀ b ∈ B, b.card = 6) (hcov : CoversTriples B) (x y : Fin 13) (hxy : x ≠ y) :
    3 ≤ (B.filter (fun b => x ∈ b ∧ y ∈ b)).card := by
  classical
  set Bxy := B.filter (fun b => x ∈ b ∧ y ∈ b) with hBxy
  -- the 11 third points are covered by the blocks through {x, y}
  have hZ : (univ \ {x, y} : Finset (Fin 13)) ⊆ Bxy.biUnion (fun b => b \ {x, y}) := by
    intro z hz
    have hz' : z ≠ x ∧ z ≠ y := by
      simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton, not_or] at hz
      exact hz
    obtain ⟨b, hb, hT⟩ := hcov {x, y, z} (by
      rw [card_insert_of_notMem, card_pair hz'.2.symm]
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hxy, hz'.1.symm⟩)
    have hxb : x ∈ b := hT (by simp)
    have hyb : y ∈ b := hT (by simp)
    have hzb : z ∈ b := hT (by simp)
    rw [mem_biUnion]
    refine ⟨b, ?_, ?_⟩
    · rw [hBxy, mem_filter]; exact ⟨hb, hxb, hyb⟩
    · rw [mem_sdiff]
      exact ⟨hzb, by simp only [mem_insert, mem_singleton, not_or]; exact hz'⟩
  have hcardZ : (univ \ {x, y} : Finset (Fin 13)).card = 11 := by
    rw [card_sdiff, inter_eq_left.mpr (subset_univ _), card_univ, Fintype.card_fin, card_pair hxy]
  have hle := card_le_card hZ
  have hbi := card_biUnion_le (s := Bxy) (t := fun b => b \ {x, y})
  have hterm : ∀ b ∈ Bxy, (b \ {x, y}).card = 4 := by
    intro b hb
    rw [hBxy, mem_filter] at hb
    have hsub : ({x, y} : Finset (Fin 13)) ⊆ b := by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hb.2.1
      · exact hb.2.2
    rw [card_sdiff, inter_eq_left.mpr hsub, hsize b hb.1, card_pair hxy]
  have hsum : ∑ b ∈ Bxy, (b \ {x, y}).card = 4 * Bxy.card := by
    rw [sum_congr rfl hterm, sum_const, smul_eq_mul, mul_comm]
  sorry

/-- Point count: every point lies in at least 8 of the 20 blocks. -/
theorem cover20_point_degree (B : Finset (Finset (Fin 13))) (hcard : B.card = 20)
    (hsize : ∀ b ∈ B, b.card = 6) (hcov : CoversTriples B) (x : Fin 13) :
    8 ≤ (B.filter (fun b => x ∈ b)).card := by
  classical
  set Bx := B.filter (fun b => x ∈ b) with hBx
  -- double count incidences (y, b) with y ≠ x, b ∈ Bx, y ∈ b
  have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ.erase x : Finset (Fin 13))) (t := Bx) (r := fun (y : Fin 13) (b : Finset (Fin 13)) => y ∈ b)
  -- each block through x has exactly 5 other points
  have hbelow : ∀ b ∈ Bx, ((univ.erase x).bipartiteBelow (fun (y : Fin 13) (b : Finset (Fin 13)) => y ∈ b) b).card = 5 := by
    intro b hb
    rw [hBx, mem_filter] at hb
    have : (univ.erase x).bipartiteBelow (fun (y : Fin 13) (b : Finset (Fin 13)) => y ∈ b) b = b.erase x := by
      ext w
      simp [bipartiteBelow, mem_filter, mem_erase] <;> tauto
    rw [this, card_erase_of_mem hb.2, hsize b hb.1]
  have hright : ∑ b ∈ Bx, ((univ.erase x).bipartiteBelow (fun (y : Fin 13) (b : Finset (Fin 13)) => y ∈ b) b).card = 5 * Bx.card := by
    rw [sum_congr rfl hbelow, sum_const, smul_eq_mul, mul_comm]
  -- each y ≠ x sees at least 3 blocks through x
  have habove : ∀ y ∈ (univ.erase x : Finset (Fin 13)), 3 ≤ (Bx.bipartiteAbove (fun (y : Fin 13) (b : Finset (Fin 13)) => y ∈ b) y).card := by
    intro y hy
    have hyx : x ≠ y := (ne_of_mem_erase hy).symm
    have : Bx.bipartiteAbove (fun (y : Fin 13) (b : Finset (Fin 13)) => y ∈ b) y = B.filter (fun b => x ∈ b ∧ y ∈ b) := by
      ext b
      simp [bipartiteAbove, hBx, mem_filter] <;> tauto
    rw [this]
    exact cover20_pair_count B hsize hcov x y hyx
  have hleft : 12 * 3 ≤ ∑ y ∈ (univ.erase x : Finset (Fin 13)), (Bx.bipartiteAbove (fun (y : Fin 13) (b : Finset (Fin 13)) => y ∈ b) y).card := by
    have h := sum_le_sum habove
    rw [sum_const, smul_eq_mul, card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin] at h
    exact h
  sorry

-- axiom footprint
#print axioms CoversTriples
#print axioms cover20_pair_count
#print axioms cover20_point_degree
