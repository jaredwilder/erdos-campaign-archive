import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def s : ℕ → ℕ := fun n => Nat.nth (fun k => Squarefree k) n

def gap (n : ℕ) : ℕ := s (n + 1) - s n
