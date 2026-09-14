import Mathlib

set_option autoImplicit false


set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem msl_proof_sidon8_kernel_close_close  : âˆ€ (S : Finset (Fin 8)), S.card = 5 â†’ Â¬ (âˆ€ a âˆˆ S, âˆ€ b âˆˆ S, âˆ€ c âˆˆ S, âˆ€ d âˆˆ S, (a.val + b.val = c.val + d.val) â†’ ((a = c âˆ§ b = d) âˆ¨ (a = d âˆ§ b = c))) := by decide

-- axiom footprint
#print axioms msl_proof_sidon8_kernel_close_close
