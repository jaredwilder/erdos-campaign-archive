import Mathlib

set_option autoImplicit false


def sums (A : List Nat) : List Nat :=
  (A.zipIdx A |>.flatMap fun (a, i) =>
    (A.zipIdx A |>.filterMap fun (b, j) =>
      if i ≤ j then some (a + b) else none))

def isSidon (A : List Nat) : Bool :=
  let s := sums A
  s.eraseDups.length == s.length

def tValue (A : List Nat) : Nat := (sums A).length

def nPairs (n : Nat) : Nat := n * (n + 1) / 2

def checkL1 (A : List Nat) : Bool :=
  isSidon A && tValue A == nPairs A.length

def witness : List Nat := [0, 1, 4, 10]

theorem msl_fmz_erdos153_campaign_001_R004_L1_a2r1  : checkL1 witness = true ∧ tValue witness = 10 ∧ nPairs 4 = 10 := by decide

-- axiom footprint
#print axioms sums
#print axioms isSidon
#print axioms tValue
#print axioms nPairs
#print axioms checkL1
#print axioms witness
#print axioms msl_fmz_erdos153_campaign_001_R004_L1_a2r1
