/-
  Erdős Problem 28 — the PARITY FLOOR.

  Kernel-checked, sorry-free:  every additive basis of order 2 satisfies
  `limsup r_A(n) ≥ 2`, i.e. `r_A(n) ≤ 1` for all large `n` is impossible.

  Mechanism: for ODD `n` the swap involution `(a,b) ↦ (b,a)` on the representations of `n`
  has no fixed point (a fixed point would force `n = 2a`), so a single representation
  immediately yields a second one.  The basis hypothesis supplies the first.

  ⛔ CLAIM CEILING — this is the FLOOR and it is FAR BELOW the published state of the art.
  Borwein–Choi–Chu (2006) proved `limsup r_A(n) ≥ 8` for every additive basis of order 2,
  building on Grekos–Haddad–Largeron–Salvi (`≥ 6`).  NEITHER is formalised here, and both
  are recorded as UNPROVED in `receipts/findings.json`.  What this file banks is a
  kernel-checked formalisation of the elementary bound `≥ 2`, not a new theorem, and the
  parity mechanism provably CANNOT be pushed past `2` (see `Erdos28Reduction.lean`,
  `parity_saturates_at_two`).

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Erdos28Core

namespace Erdos28

open Finset Filter Set
open scoped Topology Pointwise

attribute [local instance 100] Classical.propDecidable

/-- The swap `(a,b) ↦ (b,a)` preserves the set of representations of `n`. -/
theorem swap_mem_rep_set {A : Set ℕ} {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ (Finset.antidiagonal n).filter (fun q => q.1 ∈ A ∧ q.2 ∈ A)) :
    (p.2, p.1) ∈ (Finset.antidiagonal n).filter (fun q => q.1 ∈ A ∧ q.2 ∈ A) := by
  rw [Finset.mem_filter, Finset.mem_antidiagonal] at hp ⊢
  exact ⟨by omega, hp.2.2, hp.2.1⟩

/-- **The parity step.**  For ODD `n`, one representation forces two: `1 ≤ r_A(n)` implies
`2 ≤ r_A(n)`.  Equivalently `r_A(n)` is even at odd `n`, which is all that is used. -/
theorem two_le_rep_of_odd {A : Set ℕ} {n : ℕ} (hodd : Odd n) (h1 : 1 ≤ rep A n) :
    2 ≤ rep A n := by
  classical
  obtain ⟨k, hk⟩ := hodd
  rw [rep] at h1 ⊢
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h1
  have hswap := swap_mem_rep_set (A := A) (n := n) hp
  have hmem : p ∈ Finset.antidiagonal n := (Finset.mem_filter.mp hp).1
  rw [Finset.mem_antidiagonal] at hmem
  have hne : p ≠ (p.2, p.1) := by
    intro hcon
    have h2 : p.1 = p.2 := by
      have := congrArg Prod.fst hcon
      simpa using this
    omega
  exact Finset.one_lt_card.mpr ⟨p, hp, (p.2, p.1), hswap, hne⟩

/-- Odd naturals are frequent at infinity. -/
theorem frequently_odd_atTop : ∃ᶠ n : ℕ in atTop, Odd n := by
  refine Filter.frequently_atTop.mpr fun a => ⟨2 * a + 1, by omega, ⟨a, by omega⟩⟩

/-- **THE FLOOR, pointwise form.**  For every additive basis of order 2, `r_A(n) ≥ 2` holds
for every large ODD `n`. -/
theorem two_le_rep_odd_of_basis {A : Set ℕ} (hA : IsBasis2 A) :
    ∃ M : ℕ, ∀ n : ℕ, M < n → Odd n → 2 ≤ rep A n := by
  obtain ⟨M, hM⟩ := one_le_rep_of_basis hA
  exact ⟨M, fun n hn hodd => two_le_rep_of_odd hodd (hM n hn)⟩

/-- `r_A(n) ≥ 2` happens frequently along `atTop`, for every additive basis of order 2. -/
theorem frequently_two_le_rep {A : Set ℕ} (hA : IsBasis2 A) :
    ∃ᶠ n : ℕ in atTop, 2 ≤ rep A n := by
  obtain ⟨M, hM⟩ := two_le_rep_odd_of_basis hA
  have hev : ∀ᶠ n : ℕ in atTop, M < n := eventually_gt_atTop M
  exact (frequently_odd_atTop.and_eventually hev).mono fun n hn => hM n hn.2 hn.1

/-- **THE FLOOR.**  Every additive basis of order 2 has `limsup r_A(n) ≥ 2`.

This is the elementary lower pin on the Erdős–Turán conjecture, which asks for `= ⊤`. -/
theorem two_le_limsup_of_basis {A : Set ℕ} (hA : IsBasis2 A) :
    (2 : ℕ∞) ≤ limsup (fun n : ℕ => (rep A n : ℕ∞)) atTop := by
  refine le_limsup_of_frequently_le ?_
  exact (frequently_two_le_rep hA).mono fun n hn => by exact_mod_cast hn

/-- **THE FLOOR, refutation form.**  No additive basis of order 2 has `r_A(n) ≤ 1` for all
large `n`.  (The `B = 1` case of Erdős–Turán, kernel-checked.) -/
theorem not_rep_le_one_of_basis {A : Set ℕ} (hA : IsBasis2 A) :
    ¬ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → rep A n ≤ 1 := by
  rintro ⟨N₀, hN₀⟩
  obtain ⟨M, hM⟩ := two_le_rep_odd_of_basis hA
  set n : ℕ := 2 * (M + N₀) + 1 with hn
  have h2 : 2 ≤ rep A n := hM n (by omega) ⟨M + N₀, by omega⟩
  have h1 : rep A n ≤ 1 := hN₀ n (by omega)
  omega

/-- **THE FLOOR, uniform-bound form.**  A uniform bound `B` on the representation function of
an additive basis of order 2 must satisfy `2 ≤ B`.  This is the input that upgrades the
counting sandwich of `Erdos28Sandwich.lean`. -/
theorem two_le_bound_of_basis {A : Set ℕ} {B : ℕ} (hA : IsBasis2 A) (hB : ∀ n, rep A n ≤ B) :
    2 ≤ B := by
  obtain ⟨M, hM⟩ := two_le_rep_odd_of_basis hA
  have h2 : 2 ≤ rep A (2 * (M + 1) + 1) := hM _ (by omega) ⟨M + 1, by omega⟩
  exact le_trans h2 (hB _)

end Erdos28
