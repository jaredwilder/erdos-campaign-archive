import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def facRes : Finset Nat :=
  (Finset.univ : Finset (Fin 9)).powerset.image
    (fun (S : Finset (Fin 9)) => (∑ i ∈ S, (i : Nat).factorial) % 16)

theorem msl_erdos1108_lem_r001_l1_c1 (m : Nat) : 6 ≤ m → (m : Nat).factorial % 16 = 0 := by sorry
