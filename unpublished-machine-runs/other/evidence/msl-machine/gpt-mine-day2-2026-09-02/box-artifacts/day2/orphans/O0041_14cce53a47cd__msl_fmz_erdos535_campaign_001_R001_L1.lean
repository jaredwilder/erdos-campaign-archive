import Mathlib

set_option autoImplicit false


def bad (a b c : Nat) : Bool :=
  Nat.gcd a b == Nat.gcd b c && Nat.gcd a c == Nat.gcd b c

def tripleGcd (a b c : Nat) : Nat := Nat.gcd (Nat.gcd a b) c

def normBad (a b c : Nat) : Bool :=
  let g := tripleGcd a b c
  bad (a / g) (b / g) (c / g)

/-- Biconditional over all triples with entries in [6] (kernel-narrowed fragment). -/
def bicond : Bool :=
  (List.range 6).all fun i =>
  (List.range 6).all fun j =>
  (List.range 6).all fun k =>
    let a := i + 1; let b := j + 1; let c := k + 1
    bad a b c == normBad a b c

def idxOf (m : Nat) : List Nat :=
  (List.range 6).filter fun i => (m >>> i) % 2 == 1

def goodSet (m : Nat) : Bool :=
  let idx := idxOf m
  idx.all fun i => idx.all fun j => idx.all fun k =>
    !(i < j && j < k && bad (i+1) (j+1) (k+1))

def f36 : Nat :=
  ((List.range 64).filter goodSet).foldl Nat.max 0

theorem msl_fmz_erdos535_campaign_001_R001_L1  : bicond = true ∧ f36 = 3 := by decide

-- axiom footprint
#print axioms bad
#print axioms tripleGcd
#print axioms normBad
#print axioms bicond
#print axioms idxOf
#print axioms goodSet
#print axioms f36
#print axioms msl_fmz_erdos535_campaign_001_R001_L1
