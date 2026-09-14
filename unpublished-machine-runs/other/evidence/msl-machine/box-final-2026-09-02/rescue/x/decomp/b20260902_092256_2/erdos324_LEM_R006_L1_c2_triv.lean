import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

structure Cert where
  payload : Option String

def certSupplied (c : Option Cert) : Prop := c.isSome

def certScope (c : Option Cert) : Option Nat :=
  match c with
  | some _ => some 1
  | none => none

theorem msl_erdos324_lem_r006_l1_c2_triv (c : Option Cert) : certSupplied c → certScope c = some (1 : Nat) := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
