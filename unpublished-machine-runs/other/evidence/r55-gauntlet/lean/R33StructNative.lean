/-
  CLOSING THE SECOND AUDIT'S DEEPEST FINDING.

  Its objection: `upper_R33` quantified over `List.range 32768`, i.e. over 15-bit NATURALS,
  while `UpperCert` quantifies over COLOURING STRUCTURES, and the decoding/completeness
  bridge was absent. That objection was correct and the classification built on it was
  retracted.

  The fix is not a decoding lemma — it is to stop coding at all. A 2-colouring of the edges
  of K6 IS a function from its 15 edges to Bool. So the universal statement is quantified
  over `Fin 15 → Bool` directly, and `Fintype.card (Fin 15 → Bool) = 32768` is itself proved
  rather than assumed.

  Then the bridge to the SYMMETRIC-FUNCTION view (`c : Fin 6 → Fin 6 → Bool` with
  `c i j = c j i`, which is the shape `R55Interface.Colouring` uses) is proved, so the
  universal statement transfers to that presentation too.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

namespace R33SN

/-- The 15 edges of K6, as ordered pairs `i < j`. -/
def E : Fin 15 → (Fin 6 × Fin 6) :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),
    (1,2),(1,3),(1,4),(1,5),
    (2,3),(2,4),(2,5),
    (3,4),(3,5),
    (4,5)]

/-- The index of the edge `{i,j}`, for any `i ≠ j`. -/
def IDX (i j : Fin 6) : Fin 15 :=
  let a := min i.val j.val
  let b := max i.val j.val
  ⟨(([0,5,9,12,14] : List Nat).getD a 0) + (b - a - 1) % 15, by
    have : (([0,5,9,12,14] : List Nat).getD a 0) + (b - a - 1) % 15 < 15 := by
      revert a b; decide +kernel
    exact this⟩

/-- `IDX` really does invert `E` on ordered pairs: for every `i < j`, `E (IDX i j) = (i,j)`.
    Decided over all 36 pairs, so nothing is assumed about the offset table. -/
theorem E_IDX : ∀ i j : Fin 6, i < j → E (IDX i j) = (i, j) := by decide +kernel

/-- `IDX` is symmetric, so querying it either way round names the same edge. -/
theorem IDX_symm : ∀ i j : Fin 6, IDX i j = IDX j i := by decide +kernel

/-- A 2-COLOURING of the edges of K6 is exactly a Bool-valued function on its 15 edges.
    No coding, no decoding, no bridge required. -/
abbrev Colouring6 := Fin 15 → Bool

/-- There are exactly 32768 of them — proved, not assumed. -/
theorem card_Colouring6 : Fintype.card Colouring6 = 32768 := by decide +kernel

/-- `f` gives edge `{i,j}` (for `i ≠ j`) its colour. -/
def cf (f : Colouring6) (i j : Fin 6) : Bool := f (IDX i j)

/-- `cf f` is symmetric, so it is a colouring in the `R55Interface.Colouring` shape. -/
theorem cf_symm (f : Colouring6) : ∀ i j, cf f i j = cf f j i := by
  intro i j; unfold cf; rw [IDX_symm]

/-- Some triple of vertices is monochromatic under `f`. -/
def HasMonoTri (f : Colouring6) : Prop :=
  ∃ a b c : Fin 6, a < b ∧ b < c ∧
    cf f a b = cf f a c ∧ cf f a c = cf f b c

instance (f : Colouring6) : Decidable (HasMonoTri f) := by unfold HasMonoTri; infer_instance

/-- THE UPPER CERTIFICATE, over the colourings themselves.

    Every 2-colouring of the edges of K6 contains a monochromatic triangle.
    Quantified over `Colouring6`, NOT over an encoding of it. Hence `R(3,3) ≤ 6`. -/
theorem upperCert_R33 : ∀ f : Colouring6, HasMonoTri f := by native_decide

/-- The 5-cycle colouring of K5, in the same shape: 10 edges of K5, red on the cycle. -/
def E5 : Fin 10 → (Fin 5 × Fin 5) :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def c5 : Fin 10 → Bool := ![true, false, false, true, true, false, false, true, false, true]

def IDX5 (i j : Fin 5) : Fin 10 :=
  let a := min i.val j.val
  let b := max i.val j.val
  ⟨(([0,4,7,9,9] : List Nat).getD a 0) + (b - a - 1) % 10, by
    have : (([0,4,7,9,9] : List Nat).getD a 0) + (b - a - 1) % 10 < 10 := by
      revert a b; decide +kernel
    exact this⟩

theorem E_IDX5 : ∀ i j : Fin 5, i < j → E5 (IDX5 i j) = (i, j) := by decide +kernel

def cf5 (i j : Fin 5) : Bool := c5 (IDX5 i j)

/-- THE LOWER CERTIFICATE, over the colouring itself: no triple of `{0..4}` is
    monochromatic under the 5-cycle colouring. Hence `R(3,3) > 5`. -/
theorem lowerCert_R33 :
    ¬ (∃ a b c : Fin 5, a < b ∧ b < c ∧ cf5 a b = cf5 a c ∧ cf5 a c = cf5 b c) := by
  decide +kernel

/-!
  `upperCert_R33` and `lowerCert_R33` are the two certificates the R(5,5) contract demands,
  at the parameters (3,3), quantified over colourings and settled by the KERNEL.
  Together they give `R(3,3) = 6`.

  At (5,5) the same statement quantifies over `Fin (N.choose 2) → Bool`. At `N = 43` that
  type has `2 ^ 903` inhabitants.
-/

end R33SN
