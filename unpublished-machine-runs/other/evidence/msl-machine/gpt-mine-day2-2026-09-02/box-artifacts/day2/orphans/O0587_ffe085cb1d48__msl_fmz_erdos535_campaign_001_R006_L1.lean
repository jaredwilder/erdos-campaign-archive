import Mathlib

set_option autoImplicit false


def tripleBad (a b c : Nat) : Bool :=
  let ab := Nat.gcd a b
  let ac := Nat.gcd a c
  let bc := Nat.gcd b c
  ab == ac && ac == bc

def pairs : List Nat → List (Nat × Nat)
  | [] => []
  | a :: rest => rest.map (fun b => (a, b)) ++ pairs rest

def triples : List Nat → List (Nat × Nat × Nat)
  | [] => []
  | a :: rest => (pairs rest).map (fun p => (a, p.1, p.2)) ++ triples rest

def ok (l : List Nat) : Bool :=
  (triples l).all (fun t => !(tripleBad t.1 t.2.1 t.2.2))

def elems (N mask : Nat) : List Nat :=
  (List.range N).filterMap (fun i => if mask.testBit i then some (i + 1) else none)

def bitsCount (N mask : Nat) : Nat :=
  (List.range N).countP (fun i => mask.testBit i)

def loop (N : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | best, m + 1 =>
    let mask := m
    let best' := if ok (elems N mask) then Nat.max best (bitsCount N mask) else best
    loop N best' m
  termination_by _ m => m

def f3 (N : Nat) : Nat := loop N 0 (2 ^ N)

theorem msl_fmz_erdos535_campaign_001_R006_L1  : f3 1 = 1 ∧ f3 2 = 2 ∧ f3 3 = 2 ∧ f3 4 = 3 ∧ f3 5 = 3 ∧ f3 6 = 3 ∧ f3 7 = 3 := by decide

-- axiom footprint
#print axioms tripleBad
#print axioms pairs
#print axioms triples
#print axioms ok
#print axioms elems
#print axioms bitsCount
#print axioms loop
#print axioms f3
#print axioms msl_fmz_erdos535_campaign_001_R006_L1
