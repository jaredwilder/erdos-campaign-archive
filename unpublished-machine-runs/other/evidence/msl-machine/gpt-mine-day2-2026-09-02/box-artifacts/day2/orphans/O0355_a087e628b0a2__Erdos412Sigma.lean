import Mathlib

set_option autoImplicit false


/-!
Erdős 412, P0 promotion (GPT gold pack A8, audited 2026-09-01; kernel round 2026-09-02).
σ(n) ≥ n + 1 for n ≥ 2, with equality exactly at the primes; hence every iterated-σ
orbit starting at n ≥ 2 is strictly increasing. Universal invariant for the σ-orbit
meeting problem (the separate "σ(6)=6" claim in this campaign was nonsense and is not here).
-/


open ArithmeticFunction

theorem erdos412_sigma_ge (n : ℕ) (hn : 2 ≤ n) : n + 1 ≤ sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply]
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hd | hd <;> rw [hd]
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors_self n (by omega)
  have hpair : (∑ d ∈ ({1, n} : Finset ℕ), d) = 1 + n := Finset.sum_pair (by omega)
  calc n + 1 = ∑ d ∈ ({1, n} : Finset ℕ), d := by rw [hpair, add_comm]
    _ ≤ ∑ d ∈ n.divisors, d := Finset.sum_le_sum_of_subset hsub

theorem erdos412_sigma_eq_iff (n : ℕ) : sigma 1 n = n + 1 ↔ n.Prime := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
    ← Nat.sum_properDivisors_eq_one_iff_prime]
  omega

theorem erdos412_iter_ge_two (n i : ℕ) (hn : 2 ≤ n) : 2 ≤ (fun m => sigma 1 m)^[i] n := by
  induction i with
  | zero => simpa using hn
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := erdos412_sigma_ge _ ih
    omega

theorem erdos412_iter_strict (n i : ℕ) (hn : 2 ≤ n) :
    (fun m => sigma 1 m)^[i] n < (fun m => sigma 1 m)^[i + 1] n := by
  rw [Function.iterate_succ_apply']
  have := erdos412_sigma_ge _ (erdos412_iter_ge_two n i hn)
  omega

-- axiom footprint
#print axioms erdos412_sigma_ge
#print axioms erdos412_sigma_eq_iff
#print axioms erdos412_iter_ge_two
#print axioms erdos412_iter_strict
