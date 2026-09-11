/-
  Erdos 1135 (Collatz) -- FINITE COMPUTATION CERTIFICATE, aimed at the residual.

  This file is NOT a universal theorem and its status word says so
  (MSL s.26.5: a finite computation certificate is not a universal theorem).
  It certifies, by kernel evaluation only, that every n in the four RESIDUAL
  classes mod 32 below the stated bound does drop strictly below itself.

  The residual classes are exactly the classes UNREACHED by the uniform-in-j
  symbolic method of Erdos1135.lean, so this certificate attacks the named
  obstruction rather than tabulating an unaimed range.  Being unreached by that
  method never meant failing to descend, and this file is the direct evidence:
  every residual n <= 1024 does descend.
-/
import Mathlib

namespace Erdos1135Finite

/-- Byte-identical to the frozen `CollatzConjecture.collatzStep`. -/
def collatzStep (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

/-- Kernel-cheap step: pure `Nat` arithmetic, no `Even` instance to unfold. -/
def cstep (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

theorem cstep_eq (n : ℕ) : cstep n = collatzStep n := by
  unfold cstep collatzStep
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_pos (Nat.even_iff.mpr h)]
  · rw [if_neg h, if_neg (fun he => h (Nat.even_iff.mp he))]

/-- `drops f n0 x` : iterating `cstep` from `x` at most `f` times reaches a
value strictly below `n0`. -/
def drops : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, n0, x => if x < n0 then true else drops f n0 (cstep x)

theorem drops_sound :
    ∀ f n0 x, drops f n0 x = true → ∃ t, collatzStep^[t] x < n0 := by
  intro f
  induction f with
  | zero => intro n0 x h; simp [drops] at h
  | succ f ih =>
    intro n0 x h
    rw [drops] at h
    split at h
    · rename_i hlt
      exact ⟨0, by simpa using hlt⟩
    · obtain ⟨t, ht⟩ := ih n0 (cstep x) h
      refine ⟨t + 1, ?_⟩
      rw [Function.iterate_succ_apply, ← cstep_eq]
      exact ht

/-- The four residue classes mod 32 the symbolic method does not reach. -/
def isResidual (n : ℕ) : Bool :=
  n % 32 == 7 || n % 32 == 15 || n % 32 == 27 || n % 32 == 31

/-- `scan N` : every residual `n` with `1 ≤ n ≤ N` drops within the fuel. -/
def scan : ℕ → Bool
  | 0 => true
  | n + 1 => (!isResidual (n + 1) || drops 200 (n + 1) (cstep (n + 1))) && scan n

theorem scan_sound :
    ∀ N, scan N = true → ∀ n, 0 < n → n ≤ N → isResidual n = true →
      ∃ k, 0 < k ∧ collatzStep^[k] n < n := by
  intro N
  induction N with
  | zero => intro _ n h0 h1 _; omega
  | succ N ih =>
    intro h n h0 h1 hr
    rw [scan, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge n (N + 1) with hlt | hge
    · exact ih h.2 n h0 (by omega) hr
    · have hn : n = N + 1 := by omega
      subst hn
      rcases Bool.or_eq_true _ _ |>.mp h.1 with hbad | hgood
      · rw [hr] at hbad; simp at hbad
      · obtain ⟨t, ht⟩ := drops_sound _ _ _ hgood
        refine ⟨t + 1, Nat.succ_pos t, ?_⟩
        rw [Function.iterate_succ_apply, ← cstep_eq]
        exact ht

set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

/-- Kernel-evaluated finite certificate. -/
theorem scan_1024 : scan 1024 = true := by decide

/-- Every residual `n` below 1024 does drop strictly below itself.
FINITE COMPUTATION CERTIFICATE -- not a universal theorem. -/
theorem residual_drops_below_1024 :
    ∀ n, 0 < n → n ≤ 1024 → isResidual n = true →
      ∃ k, 0 < k ∧ collatzStep^[k] n < n :=
  scan_sound 1024 scan_1024

#print axioms cstep_eq
#print axioms drops_sound
#print axioms scan_sound
#print axioms scan_1024
#print axioms residual_drops_below_1024

end Erdos1135Finite
