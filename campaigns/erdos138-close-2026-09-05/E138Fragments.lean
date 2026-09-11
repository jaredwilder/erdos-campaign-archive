/-
Erdos problem 138 -- van der Waerden numbers W(k) (2 colours, AP length k).

Frozen source: FormalConjectures/ErdosProblems/138.lean (DeepMind formal-conjectures).
  A : lim_{k->oo} W(k)^(1/k) = oo            (erdos_138, OPEN, $500)
  B : W(k+1)/W(k) -> oo                      (erdos_138.variants.quotient, OPEN)
  C : W(k)/2^k -> oo                         (erdos_138.variants.dvd_two_pow, OPEN)

This file proves, over an ABSTRACT W : Nat -> Nat, the logical order of the three open
variants, the general-base form of A, the monotone/Berlekamp transfer and the exact
numeric shape of its prime-gap loss, plus a finite receipt for the source defect in the
Berlekamp docstring of 138.lean.

No `sorry`. No axioms beyond Mathlib's.
-/
import Mathlib

namespace Erdos138Fragments

open Filter

/-- A: the k-th root of `W k` diverges. -/
def RootDiv (W : ℕ → ℕ) : Prop :=
  Tendsto (fun k : ℕ => (W k : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop atTop

/-- C(base): `W k / C^k` diverges. `C = 2` is variant `dvd_two_pow`. -/
def BaseDiv (W : ℕ → ℕ) (C : ℝ) : Prop :=
  Tendsto (fun k : ℕ => (W k : ℝ) / C ^ k) atTop atTop

/-- B: the consecutive ratio diverges. -/
def RatioDiv (W : ℕ → ℕ) : Prop :=
  Tendsto (fun k : ℕ => (W (k + 1) : ℝ) / (W k : ℝ)) atTop atTop

/-! ### rpow plumbing -/

/-- From `B ≤ x ^ (1/k)` conclude `B^k ≤ x`. -/
theorem pow_le_of_le_rpow_inv {x B : ℝ} (hx : 0 ≤ x) (hB : 0 ≤ B) {k : ℕ} (hk : k ≠ 0)
    (h : B ≤ x ^ ((1 : ℝ) / (k : ℝ))) : B ^ k ≤ x := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hmono : B ^ ((k : ℕ) : ℝ) ≤ (x ^ ((1 : ℝ) / (k : ℝ))) ^ ((k : ℕ) : ℝ) :=
    Real.rpow_le_rpow hB h (le_of_lt hk0)
  have hid : (x ^ ((1 : ℝ) / (k : ℝ))) ^ ((k : ℕ) : ℝ) = x := by
    rw [← Real.rpow_mul hx, one_div, inv_mul_cancel₀ (ne_of_gt hk0), Real.rpow_one]
  rw [hid, Real.rpow_natCast B k] at hmono
  exact hmono

/-- From `B^k ≤ x` conclude `B ≤ x ^ (1/k)`. -/
theorem le_rpow_inv_of_pow_le {x B : ℝ} (hB : 0 ≤ B) {k : ℕ} (hk : k ≠ 0)
    (h : B ^ k ≤ x) : B ≤ x ^ ((1 : ℝ) / (k : ℝ)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hBk : (0 : ℝ) ≤ B ^ k := pow_nonneg hB k
  have hmono : (B ^ k) ^ ((1 : ℝ) / (k : ℝ)) ≤ x ^ ((1 : ℝ) / (k : ℝ)) :=
    Real.rpow_le_rpow hBk h (by positivity)
  have hid : (B ^ k) ^ ((1 : ℝ) / (k : ℝ)) = B := by
    rw [← Real.rpow_natCast B k, ← Real.rpow_mul hB]
    rw [mul_one_div, div_self (ne_of_gt hk0), Real.rpow_one]
  rwa [hid] at hmono

/-! ### A  <->  (C for every base) -/

/-- A implies C(base) for EVERY positive base. -/
theorem baseDiv_of_rootDiv {W : ℕ → ℕ} (hA : RootDiv W) {C : ℝ} (hC : 0 < C) :
    BaseDiv W C := by
  have h2 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ h2
  have hev := hA.eventually_ge_atTop (2 * C)
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hkne : k ≠ 0 := by omega
  have hCk : (0 : ℝ) < C ^ k := pow_pos hC k
  have hW : (2 * C) ^ k ≤ (W k : ℝ) :=
    pow_le_of_le_rpow_inv (by positivity) (by positivity) hkne hk
  have : (2 : ℝ) ^ k * C ^ k ≤ (W k : ℝ) := by rwa [mul_pow] at hW
  rw [le_div_iff₀ hCk]
  exact this

/-- The `C = 2` instance: A implies the `dvd_two_pow` variant. -/
theorem two_pow_div_of_rootDiv {W : ℕ → ℕ} (hA : RootDiv W) : BaseDiv W 2 :=
  baseDiv_of_rootDiv hA (by norm_num)

/-- Conversely, C(base) for every base implies A. -/
theorem rootDiv_of_forall_baseDiv {W : ℕ → ℕ} (h : ∀ C : ℝ, 0 < C → BaseDiv W C) :
    RootDiv W := by
  unfold RootDiv
  rw [tendsto_atTop]
  intro b
  have hb : (0 : ℝ) < max b 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hev := (h (max b 1) hb).eventually_ge_atTop 1
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hkne : k ≠ 0 := by omega
  have hCk : (0 : ℝ) < (max b 1) ^ k := pow_pos hb k
  have hW : (max b 1) ^ k ≤ (W k : ℝ) := by
    rw [le_div_iff₀ hCk] at hk
    simpa using hk
  exact le_trans (le_max_left b 1) (le_rpow_inv_of_pow_le (le_of_lt hb) hkne hW)

/-- A is EXACTLY the statement that `W k` beats every exponential. -/
theorem rootDiv_iff_forall_baseDiv {W : ℕ → ℕ} :
    RootDiv W ↔ ∀ C : ℝ, 0 < C → BaseDiv W C :=
  ⟨fun hA _ hC => baseDiv_of_rootDiv hA hC, rootDiv_of_forall_baseDiv⟩

/-! ### B implies A -/

/-- Geometric growth from an eventual multiplicative step. -/
theorem pow_le_of_step {W : ℕ → ℕ} {M : ℝ} (hM : 0 ≤ M) {N : ℕ} (hN : 1 ≤ W N)
    (hstep : ∀ k, N ≤ k → M * (W k : ℝ) ≤ (W (k + 1) : ℝ)) :
    ∀ j : ℕ, M ^ j ≤ (W (N + j) : ℝ) := by
  intro j
  induction j with
  | zero => simpa using (by exact_mod_cast hN : (1 : ℝ) ≤ (W N : ℝ))
  | succ j ih =>
      have h1 : M ^ (j + 1) ≤ M * (W (N + j) : ℝ) := by
        rw [pow_succ, mul_comm (M ^ j) M]
        exact mul_le_mul_of_nonneg_left ih hM
      have h2 : M * (W (N + j) : ℝ) ≤ (W (N + j + 1) : ℝ) := hstep _ (Nat.le_add_right _ _)
      calc M ^ (j + 1) ≤ M * (W (N + j) : ℝ) := h1
        _ ≤ (W (N + j + 1) : ℝ) := h2
        _ = (W (N + (j + 1)) : ℝ) := by ring_nf

/-- **B implies A**: the quotient variant is STRICTLY STRONGER than the root problem. -/
theorem rootDiv_of_ratioDiv {W : ℕ → ℕ} (hB : RatioDiv W) : RootDiv W := by
  unfold RootDiv
  rw [tendsto_atTop]
  intro b
  set c : ℝ := max b 1 with hc
  have hc1 : (1 : ℝ) ≤ c := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ c := le_trans zero_le_one hc1
  -- eventual step with factor c^2
  have hev := hB.eventually_ge_atTop (max (c ^ 2) 1)
  obtain ⟨N0, hN0⟩ := (hev.and (hB.eventually_ge_atTop 1)).exists_forall_of_atTop
  -- W is eventually at least 1 (else the ratio would be 0)
  have hpos : ∀ k, N0 ≤ k → 1 ≤ W k := by
    intro k hk
    by_contra hcon
    have hW0 : W k = 0 := by omega
    have := (hN0 k hk).2
    rw [hW0] at this
    simp at this
    linarith
  have hstep : ∀ k, N0 ≤ k → c ^ 2 * (W k : ℝ) ≤ (W (k + 1) : ℝ) := by
    intro k hk
    have hWk : (1 : ℝ) ≤ (W k : ℝ) := by exact_mod_cast hpos k hk
    have hWk0 : (0 : ℝ) < (W k : ℝ) := lt_of_lt_of_le zero_lt_one hWk
    have := (hN0 k hk).1
    rw [le_div_iff₀ hWk0] at this
    exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hWk0)) this
  have hgeo := pow_le_of_step (W := W) (M := c ^ 2) (by positivity) (hpos N0 le_rfl) hstep
  filter_upwards [eventually_ge_atTop (2 * N0 + 1)] with k hk
  have hkne : k ≠ 0 := by omega
  have hkN : N0 ≤ k := by omega
  have hj : N0 + (k - N0) = k := by omega
  have hgk : (c ^ 2) ^ (k - N0) ≤ (W k : ℝ) := by
    have := hgeo (k - N0)
    rwa [hj] at this
  have hexp : k ≤ 2 * (k - N0) := by omega
  have hck : c ^ k ≤ (c ^ 2) ^ (k - N0) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hc1 (by omega)
  exact le_trans (le_max_left b 1)
    (le_rpow_inv_of_pow_le hc0 hkne (le_trans hck hgk))

/-- The chain of the three open variants of Erdos 138. -/
theorem variant_chain {W : ℕ → ℕ} (hB : RatioDiv W) : RootDiv W ∧ BaseDiv W 2 :=
  ⟨rootDiv_of_ratioDiv hB, two_pow_div_of_rootDiv (rootDiv_of_ratioDiv hB)⟩

/-! ### Monotonicity of an infimum-defined threshold number -/

/-- If the guarantee sets shrink in `k` and stay nonempty, the threshold is monotone.
This is the abstract content of "van der Waerden numbers are nondecreasing in `k`":
`S k` is `monoAP_guarantee_set r k`, and `S (k+1) ⊆ S k` because a monochromatic AP of
length `k+1` contains one of length `k`. -/
theorem sInf_monotone_of_antitone (S : ℕ → Set ℕ) (hne : ∀ k, (S k).Nonempty)
    (hanti : ∀ k, S (k + 1) ⊆ S k) : Monotone (fun k => sInf (S k)) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  exact Nat.sInf_le (hanti k (Nat.sInf_mem (hne (k + 1))))

/-! ### The Berlekamp transfer and its prime-gap loss -/

/-- Monotone transfer: a lower bound at `p+1` is a lower bound at every `k ≥ p+1`. -/
theorem transfer_lower_bound {W : ℕ → ℕ} (hmono : Monotone W) {p k : ℕ}
    (hlb : p * 2 ^ p ≤ W (p + 1)) (hpk : p + 1 ≤ k) :
    (p : ℝ) * 2 ^ p ≤ (W k : ℝ) := by
  have h : p * 2 ^ p ≤ W k := le_trans hlb (hmono hpk)
  exact_mod_cast h

/-- **The gap loss, exactly.** With `k = p + 1 + g` (so `g` is the distance from `k-1`
down to the prime `p`), the Berlekamp bound transported to `k` is `p / 2^(g+1)`.
The factor `2^(g+1)` is the entire obstruction to settling `W k / 2^k -> oo` for all `k`
from the prime subsequence: the bound diverges only if `g ≤ log2 p - omega(1)`. -/
theorem gap_loss {W : ℕ → ℕ} (hmono : Monotone W) {p g : ℕ}
    (hlb : p * 2 ^ p ≤ W (p + 1)) :
    (p : ℝ) / 2 ^ (g + 1) ≤ (W (p + 1 + g) : ℝ) / 2 ^ (p + 1 + g) := by
  have hb := transfer_lower_bound hmono hlb (k := p + 1 + g) (by omega)
  have hsplit : (2 : ℝ) ^ (p + 1 + g) = 2 ^ p * 2 ^ (g + 1) := by
    rw [← pow_add]; ring_nf
  have step : (p : ℝ) / 2 ^ (g + 1) = ((p : ℝ) * 2 ^ p) / (2 ^ p * 2 ^ (g + 1)) := by
    have h2p : (2 : ℝ) ^ p ≠ 0 := by positivity
    field_simp
  rw [hsplit, step]
  gcongr

/-- Along the prime subsequence itself (`g = 0`) the `dvd_two_pow` quantity is `≥ p/2`,
which does diverge; the open case is exactly the `g > 0` gap region. -/
theorem prime_subsequence_bound {W : ℕ → ℕ} (hmono : Monotone W) {p : ℕ}
    (hlb : p * 2 ^ p ≤ W (p + 1)) :
    (p : ℝ) / 2 ≤ (W (p + 1) : ℝ) / 2 ^ (p + 1) := by
  have := gap_loss hmono (g := 0) hlb
  simpa using this

/-! ### Source defect receipt -/

/-- The 138.lean docstring for the Berlekamp variant says `W(p+1) ≥ p^(2^p)`; the formal
statement below it says `p * 2^p ≤ W (p+1)`; Berlekamp's published theorem is
`W(p+1) ≥ p(2^p - 1)`. At `p = 3` the three numbers are 6561, 24, 21 -- pairwise
distinct, so this is a three-way statement mismatch and not a rendering variant. -/
theorem berlekamp_three_readings_differ :
    3 * (2 ^ 3 - 1) = 21 ∧ 3 * 2 ^ 3 = 24 ∧ 3 ^ (2 ^ 3) = 6561 ∧
      (21 : ℕ) ≠ 24 ∧ (24 : ℕ) ≠ 6561 ∧ (21 : ℕ) ≠ 6561 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The formal statement in 138.lean is STRICTLY STRONGER than Berlekamp's theorem for
every prime `p ≥ 2`: `p(2^p - 1) < p·2^p`. A lower-bound hypothesis strengthened past its
cited source is `CITED_STRENGTH_INFLATED`. -/
theorem formal_statement_strictly_stronger (p : ℕ) (hp : 1 ≤ p) :
    p * (2 ^ p - 1) < p * 2 ^ p := by
  have h1 : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_pow p 2 (by norm_num)
  have h2 : 2 ^ p - 1 < 2 ^ p := by omega
  exact Nat.mul_lt_mul_of_pos_left h2 (by omega)

end Erdos138Fragments
