import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def erdos306R003L : Finset ℕ := {6, 10, 14, 15, 21, 22}

theorem msl_erdos306_lem_r003_l1_c3 : ∀ d ∈ erdos306R003L, 1 < d ∧ StrictMono (fun i : Fin 2 => if i = 0 then 1 else d) ∧ ((fun i : Fin 2 => if i = 0 then 1 else d) 0 = 1) ∧ (∀ i ∈ Finset.Icc 1 (Fin.last 1), ω ((fun i : Fin 2 => if i = 0 then 1 else d) i) = 2 ∧ Ω ((fun i : Fin 2 => if i = 0 then 1 else d) i) = 2) ∧ (1:ℚ)/(d) = ∑ i ∈ Finset.Icc 1 (Fin.last 1), (1:ℚ)/((fun i : Fin 2 => if i = 0 then 1 else d) i) := by sorry
