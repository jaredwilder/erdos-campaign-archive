import Mathlib

namespace OracleAutonomyFormal

theorem oracle_e9222e42ca6ca5d3d207f6cb : ¬ (∃ a0 : Fin 2, ∃ a1 : Fin 3, ∀ x : Fin 6, x.val % 2 = a0.val ∨ x.val % 3 = a1.val) := by
  native_decide

#print axioms oracle_e9222e42ca6ca5d3d207f6cb

end OracleAutonomyFormal
