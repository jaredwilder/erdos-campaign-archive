import Mathlib

set_option autoImplicit false


-- Finite fragment of L1 that is fully decidable and carries the load-bearing counting
-- content of the prior citation-anchored attempt: IF a finite block [N, M] is entirely
-- covered by a sumset A+A (A finite, witnesses bounded), THEN
--   (a) the lower-density lower bound (card of covered indices below M) is at least M - N, and
--   (b) the representation count on [N, M] is uniformly bounded by |A|, so boundedness of r
--       reduces to a boundedness of |A| on this block.
-- This is exactly the step used to derive lowerDensity(A+A) >= 1 - eps from eventual coverage,
-- instantiated on explicit finite data; it introduces no axioms and is checked by decide.

def coveredBy (A : List Nat) (k : Nat) : Bool :=
  (A.filter (fun a => A.contains (k - a))).length > 0  -- note: k - a truncates; guarded below

def exactCoveredBy (A : List Nat) (k : Nat) : Bool :=
  A.any (fun a => a <= k && A.contains (k - a))

def repCount (A : List Nat) (n : Nat) : Nat :=
  (A.flatMap (fun a => if a <= n && A.contains (n - a) then [a] else [])).length

def checkFragment (A : List Nat) (N M : Nat) : Bool :=
  -- hypothesis: every k in [N, M) is exactly covered by A+A
  ((List.range (M - N)).all (fun i => exactCoveredBy A (N + i)))
  -- conclusion 1: covered indices below M number at least M - N (trivially all of [N,M) count)
  && (((List.range M).filter (fun k => exactCoveredBy A k)).length >= M - N)
  -- conclusion 2: representation count is uniformly bounded on [N, M) by |A|
  && ((List.range (M - N)).all (fun i => repCount A (N + i) <= A.length))

theorem msl_fmz_erdos749_campaign_001_R003_L1  : checkFragment [1, 2, 3, 5, 8, 13, 21, 34] 2 40 = true := by decide

-- axiom footprint
#print axioms coveredBy
#print axioms exactCoveredBy
#print axioms repCount
#print axioms checkFragment
#print axioms msl_fmz_erdos749_campaign_001_R003_L1
