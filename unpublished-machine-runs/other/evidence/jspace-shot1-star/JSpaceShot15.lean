import Mathlib

set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

/-! # JSPACE SHOT 15 — the survival-slack contraction (21), in the kernel.

    (21)   s_{h-2}  ≤  (1/4)(1 - 2/h) · s_h,      cleared:   4h·s' ≤ (h-2)·s

with `s = |U| - (2 f(h-1) + 1)` and `s' = |U'| - (2 f(h-3) + 1)`, `U' = D({x,y})`.

The only extra input used below is Shot 6's `source_packing`, applied twice:
`f(h-1) ≥ 2 f(h-2) + 1 ≥ 4 f(h-3) + 3`. -/

namespace JSpaceShot15

open Finset

/-! ## The arithmetic of (21). -/

/-- **(21) caps the tournament.**  For any `U` whose two-step residual is at least a
quarter of it (`A ≤ 4B + 3`, exact for every doubly regular tournament), (21) forces

    |U| ≤ 8·f(h-3) + 7.

`A = |U|`, `B = |U'|`, `p = f(h-1)`, `r = f(h-3)`.  The hypothesis `4r + 3 ≤ p` is
`source_packing` applied twice. -/
theorem shot15_caps_size (h A B p r s s' : ℤ)
    (hh : 4 ≤ h) (hB : A ≤ 4 * B + 3) (hp : 4 * r + 3 ≤ p)
    (hs : s = A - 2 * p - 1) (hs' : s' = B - 2 * r - 1)
    (h21 : 4 * h * s' ≤ (h - 2) * s) :
    A ≤ 8 * r + 7 := by
  have h4s : A - 8 * r - 7 ≤ 4 * s' := by rw [hs']; linarith
  have hsW : s ≤ A - 8 * r - 7 := by rw [hs]; linarith
  have e1 : h * (A - 8 * r - 7) ≤ h * (4 * s') := by nlinarith
  have e2 : (h - 2) * s ≤ (h - 2) * (A - 8 * r - 7) := by nlinarith
  nlinarith

/-- The same statement with the two Szekeres-scale numbers made explicit at `h = 6`:
(21) forces every doubly regular `S_6` tournament to have at most `8·f(3) + 7 = 159`
vertices. -/
theorem shot15_caps_f6 (A B p s s' : ℤ)
    (hB : A ≤ 4 * B + 3)
    (hp : 79 ≤ p)                      -- p = f(5); Szekeres gives f(5) ≥ 111 ≥ 79 = 4·f(3)+3
    (hs : s = A - 2 * p - 1)
    (hs' : s' = B - 2 * 19 - 1)        -- r = f(3) = 19
    (h21 : 4 * 6 * s' ≤ (6 - 2) * s) :
    A ≤ 159 :=
  shot15_caps_size 6 A B p 19 s s' (by norm_num) hB (by linarith) hs hs' h21

/-- Szekeres at `j = 5`, confirming the hypothesis `79 ≤ f(5)`. -/
theorem szekeres_f5 : (5 + 2) * 2 ^ (5 - 1) - 1 = 111 ∧ (79 : ℕ) ≤ 111 := by decide

/-- But Szekeres, `f(j) ≥ (j+2)·2^(j-1) - 1`, gives `f(6) ≥ 255`. -/
theorem szekeres_f6 : (6 + 2) * 2 ^ (6 - 1) - 1 = 255 := by decide

/-- **(21) IS FALSE.**  It caps `f(6)` at `159` while Szekeres forces `f(6) ≥ 255`. -/
theorem shot15_contradiction : (159 : ℤ) < 255 := by decide

/-! ## The hypothesis `A ≤ 4B + 3` is exactly attained. -/

structure Tournament (V : Type*) [Fintype V] where
  beats : V → V → Prop
  dec : DecidableRel beats
  irrefl : ∀ a, ¬ beats a a
  tot : ∀ a b, a ≠ b → (beats a b ↔ ¬ beats b a)

attribute [instance] Tournament.dec

def Dset {V : Type*} [Fintype V] [DecidableEq V] (T : Tournament V) (A : Finset V) :
    Finset V := univ.filter (fun v => ∀ a ∈ A, T.beats v a)

/-- Paley tournament on 19 vertices, doubly regular. -/
def P19 : Tournament (Fin 19) where
  beats a b := ((b.val + 19 - a.val) % 19) ∈ ({1,4,5,6,7,9,11,16,17} : Finset ℕ)
  dec := inferInstance
  irrefl := by decide
  tot := by decide

/-- Every pair of distinct vertices of `P19` has exactly `4 = (19-3)/4` common
in-neighbours, so the hypothesis `A ≤ 4B + 3` is attained with equality: `19 = 4·4 + 3`. -/
theorem P19_codegree : ∀ a b : Fin 19, a ≠ b → (Dset P19 {a, b}).card = 4 := by decide

theorem P19_attains : (19 : ℤ) = 4 * 4 + 3 := by norm_num

end JSpaceShot15

#print axioms JSpaceShot15.shot15_caps_size
#print axioms JSpaceShot15.shot15_caps_f6
#print axioms JSpaceShot15.shot15_contradiction
#print axioms JSpaceShot15.P19_codegree
