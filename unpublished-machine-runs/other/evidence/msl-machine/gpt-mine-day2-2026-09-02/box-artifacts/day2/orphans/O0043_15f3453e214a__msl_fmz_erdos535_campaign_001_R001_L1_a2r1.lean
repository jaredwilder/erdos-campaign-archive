import Mathlib

set_option autoImplicit false


def tg (a b c : Nat) : Nat × Nat × Nat := (Nat.gcd a b, Nat.gcd a c, Nat.gcd b c)
def peq (a b c : Nat) : Bool := Nat.gcd a b == Nat.gcd a c && Nat.gcd a b == Nat.gcd b c
-- Bézout-exactness of the gcd: g divides a and b exactly (Nat), and normalization
-- by the common factor of all three preserves the pairwise-gcd-equality predicate.
def bezoutExact (a b : Nat) : Bool :=
  let g := Nat.gcd a b
  g * (a / g) == a && g * (b / g) == b
-- every triple from [1..12]
def trips : List (Nat × Nat × Nat) :=
  (List.range 12).flatMap fun i =>
  (List.range 12).flatMap fun j =>
  (List.range 12).map fun k => (i+1, j+1, k+1)
-- fail-closed scan: return the first witness where the biconditional fails
-- (primitive-normalized predicate == raw predicate, plus exact Bezout divisibility)
def firstBad : Option (Nat × Nat × Nat) :=
  trips.find? fun (a, b, c) =>
    let n := Nat.gcd a (Nat.gcd b c)
    peq (a/n) (b/n) (c/n) != peq a b c || !bezoutExact a b || !bezoutExact b c
-- the count of checked triples must be exactly 12*12*12 = 1728 candidate triples;
-- the distinct-triple scan (i ≤ j ≤ k, 220 ordered triples) is subsumed by this full check
def tripleCheck12 : Bool := firstBad.isNone && (trips.length == 1728)
-- finite witness: f_3(6) = 3 — brute force over subsets of {1..6}
def subsetsOf6 : List (List Nat) :=
  (List.range 64).map fun m =>
    ((List.range 6).filter fun i => (m >>> i) % 2 == 1).map (· + 1)
def badSub (s : List Nat) : Bool :=
  (s.filterSublists.any fun t => t.length == 3 &&
    let [a, b, c] := t | false
    peq a b c)
def f3le6 : Bool :=
  (subsetsOf6.all fun s => s.length <= 3 || badSub s) &&
  !(subsetsOf6.all fun s => s.length <= 2 || badSub s)

theorem msl_fmz_erdos535_campaign_001_R001_L1_a2r1  : tripleCheck12 = true && f3le6 = true := by native_decide

-- axiom footprint
#print axioms tg
#print axioms peq
#print axioms bezoutExact
#print axioms trips
#print axioms firstBad
#print axioms tripleCheck12
#print axioms subsetsOf6
#print axioms badSub
#print axioms f3le6
#print axioms msl_fmz_erdos535_campaign_001_R001_L1_a2r1
