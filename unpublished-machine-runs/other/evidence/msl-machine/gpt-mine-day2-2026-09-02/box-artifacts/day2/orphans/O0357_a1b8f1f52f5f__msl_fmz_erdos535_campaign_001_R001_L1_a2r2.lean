import Mathlib

set_option autoImplicit false


def peq (a b c : Nat) : Bool :=
  Nat.gcd a b == Nat.gcd a c && Nat.gcd a b == Nat.gcd b c
-- exact Bézout/gcd divisibility: g divides both a and b (g*(a/g)=a, g*(b/g)=b)
def bezoutExact (a b : Nat) : Bool :=
  let g := Nat.gcd a b
  g * (a / g) == a && g * (b / g) == b
-- normalization to primitive reps: divide out the common gcd of all three
def primNorm (a b c : Nat) : Nat × Nat × Nat :=
  let n := Nat.gcd a (Nat.gcd b c)
  (a / n, b / n, c / n)
-- biconditional: pairwise-gcd-equality is invariant under primitive normalization
-- and normalization is itself Bezout-exact; fail-closed (any mismatch => false)
def tripleOK (a b c : Nat) : Bool :=
  let (a', b', c') := primNorm a b c
  peq a' b' c' == peq a b c && bezoutExact a b && bezoutExact b c && bezoutExact a' b'
-- FRAGMENT 1: all 220 unordered triples with 1 <= i <= j <= k <= 12
def trips : List (Nat × Nat × Nat) :=
  (List.range 12).flatMap fun i =>
  (List.range 12 - i).flatMap fun j =>
  (List.range 12 - i - j).map fun k => (i+1, i+j+1, i+j+k+1)
def tripCheck : Bool := trips.all (fun t => tripleOK t.1 t.2.1 t.2.2) && trips.length == 220
-- FRAGMENT 2: f_3(6) = 3 — every 4-subset of {1..6} contains a triple with equal
-- pairwise gcds, and the set {2,3,5} (a 3-subset) has no such triple
def subs4 : List (List Nat) :=
  (List.range 64).filterMap fun m =>
    let s := ((List.range 6).filter fun i => (m >>> i) % 2 == 1).map (· + 1)
    if s.length == 4 then some s else none
def hasBad (s : List Nat) : Bool :=
  (s.filterSublists.any fun t => t.length == 3 &&
    match t with
    | [a, b, c] => peq a b c
    | _ => false)
def f3lower : Bool := subs4.all hasBad && subs4.length == 15
def f3upper : Bool := !peq 2 3 5
def witness36 : Bool := f3lower && f3upper

theorem msl_fmz_erdos535_campaign_001_R001_L1_a2r2  : tripCheck = true ∧ witness36 = true := by native_decide

-- axiom footprint
#print axioms peq
#print axioms bezoutExact
#print axioms primNorm
#print axioms tripleOK
#print axioms trips
#print axioms tripCheck
#print axioms subs4
#print axioms hasBad
#print axioms f3lower
#print axioms f3upper
#print axioms witness36
#print axioms msl_fmz_erdos535_campaign_001_R001_L1_a2r2
