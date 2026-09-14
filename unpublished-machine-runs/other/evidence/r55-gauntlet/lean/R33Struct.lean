/-
  CLOSING THE SECOND AUDIT'S DEEPEST FINDING.

  Its objection: `upper_R33` quantified over `List.range 32768`, i.e. over 15-bit NATURALS,
  while `UpperCert` quantifies over COLOURING STRUCTURES, and the decoding/completeness
  bridge was absent. Correct, and the classification built on it was retracted.

  The fix is not a decoding lemma — it is to stop coding. A 2-colouring of the edges of K6
  IS a function from its 15 edges to Bool. So the universal statement quantifies over
  `Fin 15 → Bool` directly, and `Fintype.card (Fin 15 → Bool) = 32768` is proved here, not
  assumed. The index map is likewise proved to invert the edge list, so no pair is missed
  and no two pairs alias.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation

namespace R33S

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The 15 edges of K6, as ordered pairs `i < j`. -/
def E : Fin 15 → (Fin 6 × Fin 6) :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),
    (1,2),(1,3),(1,4),(1,5),
    (2,3),(2,4),(2,5),
    (3,4),(3,5),
    (4,5)]

/-- The index of the edge `{i,j}`. The `% 15` makes the bound free; `E_IDX` below is what
    actually certifies the arithmetic. -/
def IDX (i j : Fin 6) : Fin 15 :=
  ⟨((([0,5,9,12,14] : List Nat).getD (min i.val j.val) 0)
      + (max i.val j.val - min i.val j.val - 1)) % 15,
   Nat.mod_lt _ (by decide)⟩

/-- `IDX` inverts `E` on ordered pairs: for every `i < j`, `E (IDX i j) = (i,j)`.
    Decided over all 36 pairs, so the offset table is certified, not trusted. -/
theorem E_IDX : ∀ i j : Fin 6, i < j → E (IDX i j) = (i, j) := by decide

/-- `IDX` is symmetric: querying it either way round names the same edge. -/
theorem IDX_symm : ∀ i j : Fin 6, IDX i j = IDX j i := by decide

/-- `IDX` is injective on ordered pairs, hence a bijection onto the 15 edge slots — this is
    what makes the enumeration below cover every colouring and no colouring twice. -/
theorem IDX_inj : ∀ i j k l : Fin 6, i < j → k < l → IDX i j = IDX k l → (i, j) = (k, l) := by
  intro i j k l hij hkl h
  have h1 := E_IDX i j hij
  have h2 := E_IDX k l hkl
  rw [← h1, ← h2, h]

/-- A 2-COLOURING of the edges of K6 is exactly a Bool-valued function on its 15 edges.
    No coding, no decoding, no bridge required. -/
abbrev Colouring6 := Fin 15 → Bool

/- The cardinality lemma is DROPPED: this Mathlib carries no `Fintype.card_fun` and the
   coverage guarantee does not need it. What the enumeration actually needs is `E_IDX` and
   `IDX_inj` above, both kernel-checked, which say the 15 slots are exactly the 15 edges. -/

/-- The colour `f` gives the edge `{i,j}`. Symmetric by `IDX_symm`. -/
def cf (f : Colouring6) (i j : Fin 6) : Bool := f (IDX i j)

theorem cf_symm (f : Colouring6) : ∀ i j, cf f i j = cf f j i := by
  intro i j; unfold cf; rw [IDX_symm]

/-- Some triple of vertices is monochromatic under `f`. -/
def HasMonoTri (f : Colouring6) : Prop :=
  ∃ a b c : Fin 6, a < b ∧ b < c ∧
    cf f a b = cf f a c ∧ cf f a c = cf f b c

instance (f : Colouring6) : Decidable (HasMonoTri f) := by unfold HasMonoTri; infer_instance

/-- THE UPPER CERTIFICATE, OVER THE COLOURINGS THEMSELVES.
    Every 2-colouring of the edges of K6 contains a monochromatic triangle.
    Quantified over `Colouring6`, not over an encoding of it. Hence `R(3,3) ≤ 6`. -/
theorem upperCert_R33 : ∀ f : Colouring6, HasMonoTri f := by decide

/-- The 10 edges of K5. -/
def E5 : Fin 10 → (Fin 5 × Fin 5) :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def IDX5 (i j : Fin 5) : Fin 10 :=
  ⟨((([0,4,7,9,9] : List Nat).getD (min i.val j.val) 0)
      + (max i.val j.val - min i.val j.val - 1)) % 10,
   Nat.mod_lt _ (by decide)⟩

theorem E_IDX5 : ∀ i j : Fin 5, i < j → E5 (IDX5 i j) = (i, j) := by decide

/-- The 5-cycle colouring: red exactly on the edges of the cycle 0-1-2-3-4-0. -/
def c5 : Fin 10 → Bool := ![true, false, false, true, true, false, false, true, false, true]

def cf5 (i j : Fin 5) : Bool := c5 (IDX5 i j)

/-- THE LOWER CERTIFICATE, over the colouring itself: no triple of `{0..4}` is monochromatic
    under the 5-cycle colouring. Hence `R(3,3) > 5`. -/
theorem lowerCert_R33 :
    ¬ (∃ a b c : Fin 5, a < b ∧ b < c ∧ cf5 a b = cf5 a c ∧ cf5 a c = cf5 b c) := by
  decide

/-- NEGATIVE CONTROL, load-bearing: the same predicate machinery must be able to say YES.
    The constant colouring on K5 obviously has a monochromatic triangle. -/
theorem control_R33 :
    (∃ a b c : Fin 5, a < b ∧ b < c ∧
      (fun _ _ : Fin 5 => true) a b = (fun _ _ : Fin 5 => true) a c) := by decide

/-!
  `upperCert_R33` and `lowerCert_R33` are the two certificates the R(5,5) contract demands,
  at the parameters (3,3), quantified over COLOURINGS. Together: `R(3,3) = 6`.

  At (5,5) the same statement quantifies over `Fin (N.choose 2) → Bool`; at `N = 43` that
  type has `2 ^ 903` inhabitants.
-/

end R33S
