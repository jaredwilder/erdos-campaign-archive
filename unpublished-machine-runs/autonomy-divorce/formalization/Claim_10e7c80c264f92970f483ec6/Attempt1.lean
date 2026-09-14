import Mathlib

namespace OracleAutonomyFormal

theorem oracle_Claim_10e7c80c264f92970f483ec6 : ¬ (∃ a0 : Fin 2, ∃ a1 : Fin 3, ∀ x : Fin 6, x.val % 2 = a0.val ∨ x.val % 3 = a1.val) := by
  native_decide

#print axioms oracle_Claim_10e7c80c264f92970f483ec6

end OracleAutonomyFormal
