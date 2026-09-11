import Mathlib

/-!
Erdős 276, P0 promotion (GPT gold pack rank 7, audited 2026-09-01; kernel round 2026-09-02).
The gcd characterization (every d divides every term iff d divides gcd(a₀, a₁)) is already
KERNEL_CHECKED in cable receipt fmz-erdos276-campaign-001-R004-L1; it is re-proved here
verbatim so the corollary is self-contained: with coprime seeds no d > 1 divides every term.
(The failed R001 receipt's own subproof was wrong; this is the audit's repair.)
-/

set_option autoImplicit false

def CommonDivisor (a : ℕ → ℕ) (d : ℕ) : Prop := ∀ n, d ∣ a n

theorem erdos276_common_divisor_iff (a : ℕ → ℕ) (hrec : ∀ n : ℕ, a (n + 2) = a (n + 1) + a n)
    (d : ℕ) : CommonDivisor a d ↔ d ∣ Nat.gcd (a 0) (a 1) := by
  constructor
  · intro hd
    exact Nat.dvd_gcd (hd 0) (hd 1)
  · intro hg n
    have h0 : d ∣ a 0 := dvd_trans hg (Nat.gcd_dvd_left (a 0) (a 1))
    have h1 : d ∣ a 1 := dvd_trans hg (Nat.gcd_dvd_right (a 0) (a 1))
    induction n using Nat.twoStepInduction with
    | zero => exact h0
    | one => exact h1
    | more n ih0 ih1 =>
        rw [hrec n]
        exact dvd_add ih1 ih0

theorem erdos276_coprime_seeds_no_common_divisor (a : ℕ → ℕ)
    (hrec : ∀ n : ℕ, a (n + 2) = a (n + 1) + a n) (hcop : Nat.gcd (a 0) (a 1) = 1)
    (d : ℕ) (hd : CommonDivisor a d) : d = 1 := by
  have h := (erdos276_common_divisor_iff a hrec d).mp hd
  rw [hcop] at h
  exact Nat.dvd_one.mp h
