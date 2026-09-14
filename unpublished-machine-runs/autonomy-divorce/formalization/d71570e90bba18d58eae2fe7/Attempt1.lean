import Mathlib

namespace OracleAutonomyFormal

def cycleRed (u v : Fin 7) : Bool :=
  decide ((u.val + 1) % 7 = v.val ∨ (v.val + 1) % 7 = u.val)

theorem oracle_d71570e90bba18d58eae2fe7 :
  ∀ S : Finset (Fin 7), S.card = 5 →
    (∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ cycleRed u v = true) ∧
    (∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ cycleRed u v = false) := by
  native_decide

#print axioms oracle_d71570e90bba18d58eae2fe7

end OracleAutonomyFormal
