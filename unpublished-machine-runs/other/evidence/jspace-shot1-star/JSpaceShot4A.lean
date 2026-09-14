import Mathlib

/-!
# JSPACE SHOT 4 — fire point 2 (fired first, as requested): the arithmetic endpoint.

Shot 4 closes its contradiction with

    (16)   k^(k+1) ≤ (k+1)^k.

It holds only for `k ≤ 2`.  For every `k ≥ 3` it is false, and it stays false:
`(16)` is exactly the claim `k ≤ (1 + 1/k)^k`, and `(1 + 1/k)^k < e` for every `k`,
so the inequality is not repairable by adjusting constants.
-/

namespace JSpaceShot4A

/-- `(16)` holds at `k = 1` and `k = 2`. -/
theorem endpoint_holds_small : 1 ^ 2 ≤ 2 ^ 1 ∧ 2 ^ 3 ≤ 3 ^ 2 := by decide

/-- `(16)` is FALSE at `k = 3`: `3^4 = 81 > 64 = 4^3`. -/
theorem endpoint_false_at_three : ¬ (3 ^ 4 ≤ 4 ^ 3) := by decide

/-- **The endpoint is unrepairable.**  For every `k ≥ 3`, `(k+1)^k < k^(k+1)`,
so `(16)` fails at every `k` in the amplification range and never recovers. -/
theorem endpoint_fails_forever : ∀ k : ℕ, 3 ≤ k → (k + 1) ^ k < k ^ (k + 1) := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · have hn : n = 2 := by omega
      subst hn; decide
    · have IH : (n + 1) ^ n < n ^ (n + 1) := ih h
      have hb : (0 : ℕ) < n + 1 := by omega
      have hp2 : (0 : ℕ) < (n + 2) ^ (n + 1) := pow_pos (by omega) _
      have hAM : n * (n + 2) < (n + 1) * (n + 1) := by nlinarith
      have hpow : (n * (n + 2)) ^ (n + 1) < ((n + 1) * (n + 1)) ^ (n + 1) :=
        Nat.pow_lt_pow_left hAM (by omega)
      have hR : ((n + 1) * (n + 1)) ^ (n + 1) = (n + 1) ^ (n + 1 + 1) * (n + 1) ^ n := by
        rw [mul_pow, ← pow_add, ← pow_add]
        congr 1
        omega
      have step2 : (n + 2) ^ (n + 1) * (n + 1) ^ n < (n + 1) ^ (n + 1 + 1) * (n + 1) ^ n := by
        calc (n + 2) ^ (n + 1) * (n + 1) ^ n
            < (n + 2) ^ (n + 1) * n ^ (n + 1) := mul_lt_mul_of_pos_left IH hp2
          _ = (n * (n + 2)) ^ (n + 1) := by rw [mul_pow]; ring
          _ < ((n + 1) * (n + 1)) ^ (n + 1) := hpow
          _ = (n + 1) ^ (n + 1 + 1) * (n + 1) ^ n := hR
      exact lt_of_mul_lt_mul_right step2 (Nat.zero_le _)

end JSpaceShot4A

#print axioms JSpaceShot4A.endpoint_holds_small
#print axioms JSpaceShot4A.endpoint_false_at_three
#print axioms JSpaceShot4A.endpoint_fails_forever
