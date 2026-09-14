/-
  THE LOWER CERTIFICATE AT ORDER 40, AIMED AT THE KERNEL.

  The connection set is the one the estate's circulant lane returned at n = 40
  and which was re-verified from the definition, outside Lean, by
  oracle/kbk/engine/frontier_bridge.py.  This file asks the KERNEL the same
  question, from the definition, with no reference to the searcher.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image

namespace R55W

/-- The closed connection set returned by the lane at order 40. -/
def S : List Nat := [1, 2, 4, 5, 7, 12, 16, 17, 18, 22, 23, 24, 28, 33, 35, 36, 38, 39]

/-- Adjacency of the circulant graph on `Z 40`, symmetric by construction. -/
def adj (i j : Nat) : Bool := ((i + 40 - j) % 40) ∈ S || ((j + 40 - i) % 40) ∈ S

/-- Is the 5-set `[a,b,c,d,e]` monochromatic of colour `b0`? -/
def mono5 (a b c d e : Nat) (b0 : Bool) : Bool :=
  (adj a b == b0) && (adj a c == b0) && (adj a d == b0) && (adj a e == b0) &&
  (adj b c == b0) && (adj b d == b0) && (adj b e == b0) &&
  (adj c d == b0) && (adj c e == b0) && (adj d e == b0)

/-- Brute force over all 5-subsets of `{0,…,39}`: is SOME 5-set monochromatic? -/
def someMono5 : Bool :=
  (List.range 40).any fun a =>
    (List.range 40).any fun b => b > a &&
      ((List.range 40).any fun c => c > b &&
        ((List.range 40).any fun d => d > c &&
          ((List.range 40).any fun e => e > d &&
            (mono5 a b c d e true || mono5 a b c d e false))))

/-- THE CERTIFICATE.  No 5-set of `{0,…,39}` is monochromatic under `adj`,
    i.e. the circulant graph on `Z 40` with connection set `S` has no `K₅` and
    no independent 5-set.  Hence `R(5,5) > 40`. -/
theorem noMonoK5_at_40 : someMono5 = false := by native_decide

end R55W
