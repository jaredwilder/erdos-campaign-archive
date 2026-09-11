import Mathlib

/-!
C(13,6,3) structural route: THE DERIVED DESIGN REDUCTION.

If `B` is a family of 6-subsets of `Fin 13` covering every 3-subset, then for
each point `x` the family obtained by deleting `x` from the blocks through `x`
is a family of 5-subsets of the remaining 12 points that covers every PAIR of
those points, and it has exactly `r x = #{b ∈ B | x ∈ b}` members.

Consequence (stated as `degree_ge_of_cover_number`): the degree of every point
is at least any lower bound on the (12,5,2) covering number.  The value of that
covering number is a separate finite computation and is NOT claimed here.

Companion to `Cover20Degree.lean`, which proves the weaker `r x ≥ 8` directly.
-/

set_option autoImplicit false

open Finset

/-- A covering: every 3-subset of `Fin 13` lies inside some block. -/
def CoversTriples (B : Finset (Finset (Fin 13))) : Prop :=
  ∀ T : Finset (Fin 13), T.card = 3 → ∃ b ∈ B, T ⊆ b

/-- The blocks through `x`. -/
def through (B : Finset (Finset (Fin 13))) (x : Fin 13) : Finset (Finset (Fin 13)) :=
  B.filter (fun b => x ∈ b)

/-- The derived family at `x`: delete `x` from every block through `x`. -/
def derived (B : Finset (Finset (Fin 13))) (x : Fin 13) : Finset (Finset (Fin 13)) :=
  (through B x).image (fun b => b.erase x)

/-- Deleting `x` is injective on blocks containing `x`. -/
theorem derived_card (B : Finset (Finset (Fin 13))) (x : Fin 13) :
    (derived B x).card = (through B x).card := by
  classical
  refine card_image_of_injOn ?_
  intro a ha b hb hab
  have ha' : x ∈ a := (mem_filter.mp ha).2
  have hb' : x ∈ b := (mem_filter.mp hb).2
  have hab' : a.erase x = b.erase x := hab
  have : insert x (a.erase x) = insert x (b.erase x) := by rw [hab']
  rwa [insert_erase ha', insert_erase hb'] at this

/-- Every member of the derived family has exactly 5 elements. -/
theorem derived_block_card (B : Finset (Finset (Fin 13)))
    (hsize : ∀ b ∈ B, b.card = 6) (x : Fin 13) :
    ∀ d ∈ derived B x, d.card = 5 := by
  classical
  intro d hd
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hd
  have hbB : b ∈ B := (mem_filter.mp hb).1
  have hxb : x ∈ b := (mem_filter.mp hb).2
  rw [card_erase_of_mem hxb, hsize b hbB]

/-- Every member of the derived family avoids `x`. -/
theorem derived_avoids (B : Finset (Finset (Fin 13))) (x : Fin 13) :
    ∀ d ∈ derived B x, x ∉ d := by
  classical
  intro d hd
  obtain ⟨b, _, rfl⟩ := mem_image.mp hd
  exact notMem_erase x b

/-- THE REDUCTION. The derived family at `x` covers every pair of points
distinct from `x`. -/
theorem derived_covers_pairs (B : Finset (Finset (Fin 13)))
    (hcov : CoversTriples B) (x y z : Fin 13)
    (hyx : y ≠ x) (hzx : z ≠ x) (hyz : y ≠ z) :
    ∃ d ∈ derived B x, y ∈ d ∧ z ∈ d := by
  classical
  have hcard : ({x, y, z} : Finset (Fin 13)).card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simpa using hyz
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hyx.symm, hzx.symm⟩
  obtain ⟨b, hb, hT⟩ := hcov {x, y, z} hcard
  have hxb : x ∈ b := hT (by simp)
  have hyb : y ∈ b := hT (by simp)
  have hzb : z ∈ b := hT (by simp)
  refine ⟨b.erase x, ?_, ?_, ?_⟩
  · exact mem_image_of_mem _ (mem_filter.mpr ⟨hb, hxb⟩)
  · exact mem_erase.mpr ⟨hyx, hyb⟩
  · exact mem_erase.mpr ⟨hzx, hzb⟩

/-- THE DEGREE BOUND, conditional on a lower bound for the (12,5,2) covering
number, phrased so no unproved arithmetic enters: if every family of 5-subsets
of `univ.erase x` that covers all pairs has at least `m` members, then `x` has
degree at least `m` in `B`. -/
theorem degree_ge_of_cover_number (B : Finset (Finset (Fin 13)))
    (hsize : ∀ b ∈ B, b.card = 6) (hcov : CoversTriples B) (x : Fin 13) (m : ℕ)
    (hm : ∀ D : Finset (Finset (Fin 13)),
            (∀ d ∈ D, d.card = 5) →
            (∀ d ∈ D, x ∉ d) →
            (∀ y z : Fin 13, y ≠ x → z ≠ x → y ≠ z → ∃ d ∈ D, y ∈ d ∧ z ∈ d) →
            m ≤ D.card) :
    m ≤ (through B x).card := by
  classical
  have := hm (derived B x) (derived_block_card B hsize x) (derived_avoids B x)
    (fun y z hy hz hyz => derived_covers_pairs B hcov x y z hy hz hyz)
  rwa [derived_card B x] at this

#print axioms derived_card
#print axioms derived_block_card
#print axioms derived_avoids
#print axioms derived_covers_pairs
#print axioms degree_ge_of_cover_number
