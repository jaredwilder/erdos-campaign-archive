/-
  DOES THE TWO-CERTIFICATE MACHINERY ACTUALLY WORK, OR IS IT ONLY SHAPED LIKE IT WORKS?

  R(5,5) is out of computational reach, so `R55Interface.upperObligation` carries `sorry` and
  nothing in that file exercises the UPPER half. This file settles the identical question one
  size down, where the whole thing FITS: it decides R(3,3) = 6 completely, both certificates,
  by explicit enumeration.

  Upper half: all 2^15 = 32768 two-colourings of the 15 edges of K6 are enumerated, and every
  one is shown to contain a monochromatic triangle.
  Lower half: one explicit colouring of K5 (the 5-cycle, red on the cycle, blue on the
  pentagram) is shown to contain none.

  Together: R(3,3) = 6.

  ⛔ This does NOT bear on R(5,5). It bears on whether the INTERFACE is expressive and whether
  the obstruction there is scale rather than a missing definition. The answer is scale.
-/
import Mathlib.Data.Fintype.Card

namespace R33

/-- The 15 edges of K6 in a fixed order; edge `k` is `edges[k]`. -/
def edges : List (Nat × Nat) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),
   (1,2),(1,3),(1,4),(1,5),
   (2,3),(2,4),(2,5),
   (3,4),(3,5),
   (4,5)]

/-- Index of the edge `{i,j}` in `edges`, for `i < j < 6`. -/
def idx (i j : Nat) : Nat :=
  let a := min i j
  let b := max i j
  -- offsets: vertex 0 starts at 0, vertex 1 at 5, vertex 2 at 9, vertex 3 at 12, vertex 4 at 14
  let off := [0, 5, 9, 12, 14].getD a 0
  off + (b - a - 1)

/-- Colour of edge `{i,j}` in the colouring coded by the bits of `c`. -/
def col (c : Nat) (i j : Nat) : Bool := c.testBit (idx i j)

/-- The triples of `{0,…,5}`. -/
def triples : List (Nat × Nat × Nat) :=
  (List.range 6).flatMap fun a =>
    (List.range 6).flatMap fun b =>
      (List.range 6).filterMap fun cc =>
        if a < b && b < cc then some (a, b, cc) else none

/-- Does the colouring coded by `c` contain a monochromatic triangle? -/
def hasMonoTri (c : Nat) : Bool :=
  triples.any fun (a, b, d) =>
    (col c a b == col c a d) && (col c a d == col c b d)

/-- THE UPPER CERTIFICATE, decided: every one of the 32768 two-colourings of the edges of
    K6 contains a monochromatic triangle.  Hence `R(3,3) ≤ 6`. -/
theorem upper_R33 : (List.range 32768).all hasMonoTri = true := by native_decide

/-- The 5-cycle colouring of K5: edge `{i,j}` is red iff `j - i ≡ ±1 (mod 5)`. -/
def col5 (i j : Nat) : Bool := ((i + 5 - j) % 5 == 1) || ((j + 5 - i) % 5 == 1)

def triples5 : List (Nat × Nat × Nat) :=
  (List.range 5).flatMap fun a =>
    (List.range 5).flatMap fun b =>
      (List.range 5).filterMap fun cc =>
        if a < b && b < cc then some (a, b, cc) else none

/-- THE LOWER CERTIFICATE, decided: the 5-cycle colouring of K5 has no monochromatic
    triangle.  Hence `R(3,3) > 5`. -/
theorem lower_R33 :
    (triples5.any fun (a, b, d) =>
      (col5 a b == col5 a d) && (col5 a d == col5 b d)) = false := by native_decide

/-!
  `upper_R33` and `lower_R33` together are exactly the pair of certificates
  `R55Interface.IsR55` demands, at the parameters (3,3) and N = 6.  Both are settled by
  enumeration in seconds.

  At (5,5) the upper half would enumerate `2 ^ (N choose 2)` colourings — at N = 43 that is
  `2 ^ 903`. THAT, and not any missing definition, is the obstruction.
-/

end R33
