import Mathlib

set_option autoImplicit false


set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem msl_run19_close_sidon8_k5  : ∀ (S : Finset (Fin 8)), S.card = 5 → ¬ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, (a.val + b.val = c.val + d.val) → ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) := by decide

-- axiom footprint
#print axioms msl_run19_close_sidon8_k5
