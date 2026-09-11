/-
  Erdős Problem 28 — the campaign state in ONE kernel-checked object.

  `campaign_state` conjoins the three facts this campaign banks:

    1. THE FLOOR      every additive basis of order 2 has `limsup r_A ≥ 2`;
    2. THE KILL       the parity route that produced the floor is consistent with the
                      bound `2`, so it cannot produce `3`;
    3. THE GAP        Erdős 28 is exactly the statement that EVERY bound `B` is exceeded.

  Together: the floor is `2`, the floor cannot be raised by the route that reached it, and
  the target is `⊤`.  **Erdős 28 is UNRESOLVED by this campaign.**

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Erdos28Reduction

namespace Erdos28

open Filter
open scoped Topology Pointwise

/-- **THE CAMPAIGN STATE.**  Floor `2`, route dead at `2`, target `⊤`. -/
theorem campaign_state :
    (∀ A : Set ℕ, IsBasis2 A → (2 : ℕ∞) ≤ limsup (fun n : ℕ => (rep A n : ℕ∞)) atTop) ∧
    (∃ f : ℕ → ℕ, MomentAdmissible f ∧ ∀ n, f n ≤ 2) ∧
    (Erdos28Stmt ↔ ∀ A : Set ℕ, IsBasis2 A → ∀ B : ℕ, ∃ n, B < rep A n) :=
  ⟨fun _ hA => two_le_limsup_of_basis hA,
   parity_and_moment_saturate_at_two,
   erdos28_iff_every_bound_exceeded⟩

/-- **The gap, named.**  Every bound `B ≥ 2` is consistent with everything proved here: the
counterexample structure theorem constrains a counterexample but does not exclude one.  This
statement is the honest terminal: the campaign proves the floor and the structure, and leaves
the target open. -/
theorem what_remains :
    Erdos28Stmt ↔
      ¬ ∃ (A : Set ℕ) (B M : ℕ),
          IsBasis2 A ∧ 2 ≤ B ∧ (∀ n, rep A n ≤ B) ∧
          ∀ N : ℕ, N - M ≤ cnt A N * cnt A N ∧ cnt A N * cnt A N ≤ B * (2 * N + 1) :=
  erdos28_iff_no_theta_sqrt_basis

end Erdos28
