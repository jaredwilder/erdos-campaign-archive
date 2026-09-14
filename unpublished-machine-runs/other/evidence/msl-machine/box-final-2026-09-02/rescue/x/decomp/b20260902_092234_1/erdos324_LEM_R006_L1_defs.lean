import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

structure Cert where
  payload : Option String

def certSupplied (c : Option Cert) : Prop := c.isSome

def certScope (c : Option Cert) : Option Nat :=
  match c with
  | some _ => some 1
  | none => none
