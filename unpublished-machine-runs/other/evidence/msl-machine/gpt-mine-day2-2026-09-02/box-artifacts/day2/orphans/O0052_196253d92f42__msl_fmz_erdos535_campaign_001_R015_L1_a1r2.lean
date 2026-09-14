import Mathlib

set_option autoImplicit false



def bad3 (a b c : Nat) : Bool := let g1 := Nat.gcd a b; let g2 := Nat.gcd a c; let g3 := Nat.gcd b c; g1 == g2 && g2 == g3
def triples (N : Nat) : List (Nat × Nat × Nat) :=
  (List.range N).flatMap fun i =>
  (List.range N).flatMap fun j =>
  (List.range N).filterMap fun k =>
    let a := i + 1; let b := j + 1; let c := k + 1
    if a < b && b < c then some (a, b, c) else none
def good (N : Nat) (S : List Nat) : Bool :=
  (triples N).all fun t => !(t.1 ∈ S && t.2.1 ∈ S && t.2.2 ∈ S && bad3 t.1 t.2.1 t.2.2)
def subs : List Nat → List (List Nat)
  | [] => [[]]
  | a :: l => let s := subs l; s ++ s.map (fun t => a :: t)
def maxGood (N : Nat) : Nat :=
  ((subs (List.range N)).filter (good N)).map (fun S => S.length) |>.foldl max 0
def checkN (N : Nat) : Bool :=
  let m := maxGood N
  (subs (List.range N)).any (fun S => good N S && S.length == m)
  && (subs (List.range N)).all (fun S => !(m < S.length && good N S))
def check : Bool := (List.range 6).all (fun k => checkN (k + 3))

theorem msl_fmz_erdos535_campaign_001_R015_L1_a1r2  : check = true := by decide

-- axiom footprint
#print axioms bad3
#print axioms triples
#print axioms good
#print axioms subs
#print axioms maxGood
#print axioms checkN
#print axioms check
#print axioms msl_fmz_erdos535_campaign_001_R015_L1_a1r2
