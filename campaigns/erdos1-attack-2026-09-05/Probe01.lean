import Mathlib

/-!
PROBE 01 — Erdos #1 (distinct subset sums).
Question this probe answers, BEFORE any attack is written:
  can the Lean 4 KERNEL afford `decide` on the three finite objects the attack needs?
    P1  the 5-element witness  {6,9,11,12,13}      (2^5  = 32 subsets)
    P2  the 9-element witness  Conway-Guy at 161   (2^9  = 512 subsets)
    P3  the exhaustion over 5-subsets of [1,12]    (2^12 = 4096 powerset, 792 of card 5)
If P3 is unaffordable the exhaustion must be re-encoded on `List` instead of `Finset`.
`native_decide` is FORBIDDEN in this estate; only `decide` (real kernel reduction) is used.
-/

open Finset

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

-- P1: 5-element witness, image card
theorem probe_p1 : (({6,9,11,12,13} : Finset ℕ).powerset.image (fun S => S.sum id)).card = 32 := by
  decide

-- P2: 9-element Conway-Guy witness at 161, image card
theorem probe_p2 :
    ((({77,117,137,148,154,157,159,160,161} : Finset ℕ)).powerset.image
      (fun S => S.sum id)).card = 512 := by
  decide

-- P3: exhaustion. No 5-subset of [1,12] has 32 distinct subset sums.
theorem probe_p3 :
    ((Finset.Icc 1 12).powerset.filter
      (fun A => A.card = 5 ∧ (A.powerset.image (fun S => S.sum id)).card = 32)) = ∅ := by
  decide

#print axioms probe_p1
#print axioms probe_p2
#print axioms probe_p3
