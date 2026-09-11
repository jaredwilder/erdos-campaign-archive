import Mathlib

/-!
Erdős 313, P0 promotion (GPT gold pack A10, audited 2026-09-01; kernel round 2026-09-02).
If an Egyptian-prime solution 1/p₁+...+1/pₖ = 1 - 1/m begins (2, 3, p), then
1/p + 1/m = 1/6, so m(p-6) = 6p, so (p-6) ∣ 36, and the only prime p > 6 with that
property is p = 7. A reusable branch-kill for the fixed-head search.
-/

set_option autoImplicit false

theorem erdos313_head_prune (p : ℕ) (hp : p.Prime) (h6 : 6 < p) (hd : (p - 6) ∣ 36) : p = 7 := by
  have hle : p - 6 ≤ 36 := Nat.le_of_dvd (by norm_num) hd
  have hp42 : p ≤ 42 := by omega
  interval_cases p <;> revert hp hd <;> norm_num

theorem erdos313_head_m (p m : ℕ) (hp : p.Prime) (h6 : 6 < p) (hm : m * (p - 6) = 6 * p) :
    p = 7 := by
  have h1 : (p - 6) ∣ 6 * p := Dvd.intro_left m hm
  have h2 : (p - 6) ∣ (p - 6) * 6 := Dvd.intro 6 rfl
  have h3 : (p - 6) ∣ 6 * p - (p - 6) * 6 := Nat.dvd_sub h1 h2
  have h4 : 6 * p - (p - 6) * 6 = 36 := by omega
  rw [h4] at h3
  exact erdos313_head_prune p hp h6 h3
