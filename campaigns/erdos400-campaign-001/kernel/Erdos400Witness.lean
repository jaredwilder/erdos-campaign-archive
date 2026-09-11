import Mathlib

/-!
Erdős 400, P0 promotion (GPT gold pack A2, audited 2026-09-01; kernel round 2026-09-02).
The universal witness for g_k(m!) ≥ m + k - 3: the tuple (m! - 1, m, 1, ..., 1) has
factorial product (m!-1)! · m! · 1 = (m!)!, which divides (m!)! exactly, and its
coordinate sum exceeds n = m! by exactly m + k - 3. The existing cable receipt checked
only m = 5, k = 2; this is the all-m, all-k statement.
-/

set_option autoImplicit false

theorem erdos400_factorial_identity (m : ℕ) :
    m.factorial * (m.factorial - 1).factorial = (m.factorial).factorial :=
  Nat.mul_factorial_pred (Nat.factorial_ne_zero m)

theorem erdos400_witness_divides (m : ℕ) :
    (m.factorial - 1).factorial * m.factorial ∣ (m.factorial).factorial :=
  Dvd.intro 1 (by rw [mul_one, mul_comm]; exact Nat.mul_factorial_pred (Nat.factorial_ne_zero m))

theorem erdos400_witness_excess (m k : ℕ) (hm : 1 ≤ m) (hk : 2 ≤ k) :
    (m.factorial - 1) + m + (k - 2) - m.factorial = m + k - 3 := by
  have := Nat.factorial_pos m
  omega
