import Mathlib

/-! # JSPACE SHOT 14 — MULT at the Szekeres boundary, in the kernel.

    MULT :  C(N,2) · C(l,2)  ≤  N · C(N - 1 - m, 3)

with `N = f(k)`, `m = f(k-1)`, `l = f(k-2)`.

Shot 14's own instruction: "If it already holds at Szekeres, Shot 14 dies immediately."
Below, `N`, `m`, `l` are set to the Szekeres values `f(j) ≥ (j+2)2^(j-1) - 1` and the
inequality is evaluated exactly by the kernel. -/

set_option maxRecDepth 4000000

namespace JSpaceShot14

def binom (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

theorem binom_eq (n k : ℕ) : Nat.choose n k = binom n k :=
  Nat.choose_eq_descFactorial_div_factorial n k

/-- The Szekeres lower bound `f(j) ≥ (j+2)·2^(j-1) - 1`. -/
def szek (j : ℕ) : ℕ := (j + 2) * 2 ^ (j - 1) - 1

/-- MULT's left side at the Szekeres values. -/
def L (k : ℕ) : ℕ := Nat.choose (szek k) 2 * Nat.choose (szek (k - 2)) 2

/-- MULT's right side at the Szekeres values. -/
def R (k : ℕ) : ℕ := szek k * Nat.choose (szek k - 1 - szek (k - 1)) 3

theorem L_eq (k : ℕ) : L k = binom (szek k) 2 * binom (szek (k - 2)) 2 := by
  unfold L; rw [binom_eq, binom_eq]

theorem R_eq (k : ℕ) : R k = szek k * binom (szek k - 1 - szek (k - 1)) 3 := by
  unfold R; rw [binom_eq]

/-! ## The boundary test.  MULT holds at every Szekeres value tested. -/

theorem mult_at_szekeres_4   : L 4   ≤ R 4   := by rw [L_eq, R_eq]; decide
theorem mult_at_szekeres_5   : L 5   ≤ R 5   := by rw [L_eq, R_eq]; decide
theorem mult_at_szekeres_6   : L 6   ≤ R 6   := by rw [L_eq, R_eq]; decide
theorem mult_at_szekeres_8   : L 8   ≤ R 8   := by rw [L_eq, R_eq]; decide
theorem mult_at_szekeres_10  : L 10  ≤ R 10  := by rw [L_eq, R_eq]; decide
theorem mult_at_szekeres_20  : L 20  ≤ R 20  := by rw [L_eq, R_eq]; decide
theorem mult_at_szekeres_50  : L 50  ≤ R 50  := by rw [L_eq, R_eq]; decide
theorem mult_at_szekeres_100 : L 100 ≤ R 100 := by rw [L_eq, R_eq]; decide
theorem mult_at_szekeres_200 : L 200 ≤ R 200 := by rw [L_eq, R_eq]; decide
theorem mult_at_szekeres_500 : L 500 ≤ R 500 := by rw [L_eq, R_eq]; decide

/-! ## And the slack does not grow.  It collapses to a constant. -/

theorem margin_bounded_100 : 2 * R 100 ≤ 3 * L 100 := by rw [L_eq, R_eq]; decide
theorem margin_bounded_200 : 2 * R 200 ≤ 3 * L 200 := by rw [L_eq, R_eq]; decide
theorem margin_bounded_500 : 2 * R 500 ≤ 3 * L 500 := by rw [L_eq, R_eq]; decide

end JSpaceShot14

#print axioms JSpaceShot14.mult_at_szekeres_4
#print axioms JSpaceShot14.mult_at_szekeres_10
#print axioms JSpaceShot14.mult_at_szekeres_100
#print axioms JSpaceShot14.mult_at_szekeres_500
#print axioms JSpaceShot14.margin_bounded_500
