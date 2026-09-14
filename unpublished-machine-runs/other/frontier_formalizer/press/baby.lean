import Mathlib

/-!
THE FIRST COMPOSED SENTENCE - "mama" - 2026-08-30 night.

Two words from two independently certified formalizations of two different open Erdos problems:
  E100.Admissible      (erdos-100: pairwise distances >= 1, distinct distances separated >= 1)
  E101.noFiveOnALine   (erdos-101: no five points collinear)
Both speak the same type: Finset (Q x Q). The press conjoins them and proves the THREE Venn
witnesses that make the conjunction non-trivial (satisfiable; neither conjunct redundant).
Every def below is copied VERBATIM from its certified source file; only theorems were stripped.
-/

noncomputable section
open scoped BigOperators
open scoped Classical

namespace E100

abbrev Point := ℚ × ℚ

def euclideanDistance (p q : Point) : ℝ :=
  Real.sqrt (((p.1 : ℝ) - q.1) ^ 2 + ((p.2 : ℝ) - q.2) ^ 2)

def Admissible (P : Finset Point) : Prop :=
  (∀ p ∈ P, ∀ q ∈ P, p ≠ q →
    1 ≤ euclideanDistance p q) ∧
  (∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, ∀ s ∈ P,
    euclideanDistance p q ≠ euclideanDistance r s →
      1 ≤ |euclideanDistance p q - euclideanDistance r s|)

end E100

namespace E101

abbrev Point := ℚ × ℚ

def collinear (a b c : Point) : Prop :=
  (a.1 - b.1) * (c.2 - b.2) = (a.2 - b.2) * (c.1 - b.1)

def allCollinear (S : Finset Point) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, collinear a b c

def noFiveOnALine (P : Finset Point) : Prop :=
  ∀ S ∈ P.powerset, S.card ≠ 5 ∨ ¬ allCollinear S

end E101

namespace Press

/-- The baby's first sentence: point sets that satisfy BOTH problems' hypotheses at once. -/
def Baby (P : Finset (ℚ × ℚ)) : Prop :=
  E100.Admissible P ∧ E101.noFiveOnALine P

/-- Any set with fewer than five points trivially has no five on a line. Proved once,
    used by two witnesses. -/
theorem noFive_of_small {P : Finset (ℚ × ℚ)} (h : P.card < 5) : E101.noFiveOnALine P := by
  intro S hS
  left
  have hsub := Finset.mem_powerset.mp hS
  have := Finset.card_le_card hsub
  omega

/-- VENN CELL 1 - the sentence is satisfiable: two points at distance 1. -/
theorem baby_holds :
    Baby ({(0, 0), (1, 0)} : Finset (ℚ × ℚ)) := by
  constructor
  · norm_num [E100.Admissible, E100.euclideanDistance]
  · apply noFive_of_small
    norm_num

/-- VENN CELL 2 - `noFiveOnALine` is NOT redundant: five collinear points with integer
    coordinates 0,1,3,7,15 are Admissible (all pairwise distances are distinct integers >= 1)
    yet all five lie on the x-axis. -/
def fiveLine : Finset (ℚ × ℚ) := {(0, 0), (1, 0), (3, 0), (7, 0), (15, 0)}

theorem admissible_but_five :
    E100.Admissible fiveLine ∧ ¬ E101.noFiveOnALine fiveLine := by
  constructor
  · norm_num [E100.Admissible, E100.euclideanDistance, fiveLine]
  · intro h
    rcases h fiveLine (Finset.mem_powerset.mpr (Finset.Subset.refl _)) with h5 | hcol
    · exact h5 (by norm_num [fiveLine])
    · apply hcol
      intro a ha b hb c hc
      fin_cases ha <;> fin_cases hb <;> fin_cases hc <;>
        norm_num [E101.collinear]

/-- VENN CELL 3 - `Admissible` is NOT redundant: two points at distance 1/2 break
    admissibility while trivially having no five on a line. -/
theorem noFive_but_inadmissible :
    E101.noFiveOnALine ({(0, 0), ((1 : ℚ) / 2, 0)} : Finset (ℚ × ℚ)) ∧
      ¬ E100.Admissible ({(0, 0), ((1 : ℚ) / 2, 0)} : Finset (ℚ × ℚ)) := by
  constructor
  · apply noFive_of_small
    norm_num
  · norm_num [E100.Admissible, E100.euclideanDistance]

end Press

end
