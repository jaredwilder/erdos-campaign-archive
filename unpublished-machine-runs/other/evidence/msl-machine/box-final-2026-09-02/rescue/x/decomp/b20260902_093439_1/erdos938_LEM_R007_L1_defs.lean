import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def IsAP3 (a b c : Nat) : Prop := a + c = 2 * b

def TripleIsAP (k : Nat) : Prop :=
  ({nth Powerful k, nth Powerful (k + 1), nth Powerful (k + 2)} : Finset Nat).IsAPOfLength 3

def ApK : Set Nat := {k : Nat | TripleIsAP k}
