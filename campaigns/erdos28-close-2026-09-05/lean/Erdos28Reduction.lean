/-
  Erdős Problem 28 — the counterexample structure theorem, and the KILL of the parity route.

  Two kernel-checked, sorry-free results:

  1. `counterexample_structure` — everything this campaign proves about a hypothetical
     counterexample to the Erdős–Turán conjecture, in one object: it is an additive basis of
     order 2, its representation bound `B` satisfies `2 ≤ B`, and its counting function is
     trapped `√(N−M) ≤ |A ∩ [0,N]| ≤ √(B(2N+1))`.

  2. `parity_saturates_at_two` — an explicit KILL THEOREM for the route that produced the
     floor.  The parity mechanism supplies exactly two facts about `r_A`: it is `≥ 1` at
     every large `n` (the basis hypothesis) and it is EVEN at every odd `n` (the swap
     involution has no fixed point there).  An explicit function satisfies both while being
     bounded by `2`.  Therefore NO argument using only those two facts can prove
     `limsup r_A ≥ 3`, and the parity route to Erdős 28 is dead at the value `2`, not merely
     stalled.  This is `ROUTE_STATUS KILLED_BY_THEOREM`, kernel-checked.

  Mathlib: v4.31.0-rc1 (rev 919544d4309104b3f19724b0e6e48c701d27948f).
-/
import Erdos28Sandwich

namespace Erdos28

open Finset Filter Set
open scoped Topology Pointwise

attribute [local instance 100] Classical.propDecidable

/-! ## The counterexample structure theorem -/

/-- **THE STRUCTURE THEOREM.**  If Erdős 28 is false, a counterexample carries all of:
an additive basis of order 2, a uniform representation bound `B ≥ 2`, and a two-sided
`Θ(√N)` pin on its counting function. -/
theorem counterexample_structure (h : ¬ Erdos28Stmt) :
    ∃ (A : Set ℕ) (B M : ℕ),
      IsBasis2 A ∧ 2 ≤ B ∧ (∀ n, rep A n ≤ B) ∧
      ∀ N : ℕ, N - M ≤ cnt A N * cnt A N ∧ cnt A N * cnt A N ≤ B * (2 * N + 1) := by
  rw [Erdos28Stmt] at h
  push_neg at h
  obtain ⟨A, hA, hne⟩ := h
  obtain ⟨B, hB⟩ := rep_bdd_of_limsup_ne_top hne
  obtain ⟨hB2, M, hM⟩ := counterexample_sandwich hA hB
  exact ⟨A, B, M, hA, hB2, hB, hM⟩

/-- **Restated as a reduction.**  Erdős 28 is equivalent to: no additive basis of order 2 has
a `Θ(√N)` counting function together with a uniform representation bound.  The `Θ(√N)` clause
is FREE — it is implied by the other two — so the target loses no generality by assuming it. -/
theorem erdos28_iff_no_theta_sqrt_basis :
    Erdos28Stmt ↔
      ¬ ∃ (A : Set ℕ) (B M : ℕ),
          IsBasis2 A ∧ 2 ≤ B ∧ (∀ n, rep A n ≤ B) ∧
          ∀ N : ℕ, N - M ≤ cnt A N * cnt A N ∧ cnt A N * cnt A N ≤ B * (2 * N + 1) := by
  constructor
  · rintro H ⟨A, B, M, hA, -, hB, -⟩
    exact (erdos28_iff_no_bounded_basis.mp H) ⟨A, B, hA, hB⟩
  · intro H
    by_contra hcon
    exact H (counterexample_structure hcon)

/-! ## The kill theorem for the parity route -/

/-- The two facts the parity route extracts about the representation function of an additive
basis of order 2: it is everywhere positive, and it is even at every odd argument. -/
def ParityAdmissible (f : ℕ → ℕ) : Prop :=
  (∀ n, 1 ≤ f n) ∧ (∀ n, Odd n → 2 ∣ f n)

/-- The representation function of an additive basis of order 2 is parity-admissible on the
tail — this is exactly what `Erdos28Parity.lean` proves, restated as the route's hypothesis
set. -/
theorem parityAdmissible_shifted_rep {A : Set ℕ} (hA : IsBasis2 A) :
    ∃ M : ℕ, (∀ n, M < n → 1 ≤ rep A n) ∧ (∀ n, M < n → Odd n → 2 ≤ rep A n) := by
  obtain ⟨M, hM⟩ := one_le_rep_of_basis hA
  exact ⟨M, hM, fun n hn hodd => two_le_rep_of_odd hodd (hM n hn)⟩

/-- The explicit parity-admissible function bounded by `2`. -/
def parityWitness : ℕ → ℕ := fun n => if Odd n then 2 else 1

theorem parityWitness_admissible : ParityAdmissible parityWitness := by
  constructor
  · intro n
    unfold parityWitness
    split <;> omega
  · intro n hn
    unfold parityWitness
    rw [if_pos hn]

theorem parityWitness_le_two : ∀ n, parityWitness n ≤ 2 := by
  intro n
  unfold parityWitness
  split <;> omega

/-- **THE KILL THEOREM.**  The parity route saturates at `2`.

There is a function satisfying every constraint the parity argument places on the
representation function of an additive basis of order 2 — positivity everywhere, evenness at
every odd argument — and bounded by `2`.  Hence no deduction from those constraints alone can
yield `limsup r_A ≥ 3`, and in particular the elementary floor of `Erdos28Parity.lean` cannot
be improved without a genuinely new input.

`ROUTE_STATUS KILLED_BY_THEOREM`, not `BLOCKED_CURRENT_TECHNIQUE`. -/
theorem parity_saturates_at_two :
    ∃ f : ℕ → ℕ, ParityAdmissible f ∧ ∀ n, f n ≤ 2 :=
  ⟨parityWitness, parityWitness_admissible, parityWitness_le_two⟩

/-- **The kill, in the form the campaign consumes it.**  No proposition of the shape
"every parity-admissible function is unbounded" — nor "every parity-admissible function
exceeds `2` somewhere" — is true.  The parity constraints are consistent with the bound `2`,
so they cannot decide Erdős 28. -/
theorem not_parityAdmissible_implies_three :
    ¬ ∀ f : ℕ → ℕ, ParityAdmissible f → ∃ n, 3 ≤ f n := by
  intro H
  obtain ⟨n, hn⟩ := H parityWitness parityWitness_admissible
  have := parityWitness_le_two n
  omega

/-! ## The kill, extended along the moment axis

Ruzsa, *A just basis*, Monatsh. Math. **109** (1990), 145–151, constructs an additive basis of
order 2 whose representation function satisfies `∑_{n ≤ N} r_A(n)² = O(N)` — the second moment
of a real basis can be as small as the first moment allows.  So the second moment cannot
force unboundedness either.  The mechanical form of that obstruction is below: the same
explicit function that defeats the parity route ALSO satisfies every second-moment bound of
the shape `∑_{n < N} f(n)² ≤ C·N`, while staying bounded by `2`.

CITED, VERIFICATION_DEPTH STATEMENT_MATCHES: the Ruzsa construction itself is NOT formalised
here, and nothing below depends on it.  It is named because it is the reason the moment axis
is the right one to kill. -/

/-- The parity constraints together with a linear second-moment bound. -/
def MomentAdmissible (f : ℕ → ℕ) : Prop :=
  (∀ n, 1 ≤ f n) ∧ (∀ n, Odd n → 2 ∣ f n) ∧
    ∃ C : ℕ, ∀ N : ℕ, ∑ n ∈ Finset.range N, (f n) ^ 2 ≤ C * N

theorem parityWitness_moment (N : ℕ) :
    ∑ n ∈ Finset.range N, (parityWitness n) ^ 2 ≤ 4 * N := by
  calc ∑ n ∈ Finset.range N, (parityWitness n) ^ 2
      ≤ ∑ _n ∈ Finset.range N, 4 := by
        refine Finset.sum_le_sum fun n _ => ?_
        have := parityWitness_le_two n
        nlinarith [this]
    _ = 4 * N := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

/-- **THE KILL, EXTENDED.**  Positivity, parity, AND a linear second-moment bound are jointly
consistent with `r_A ≤ 2`.  No argument built from those three facts alone can prove
`limsup r_A ≥ 3`, let alone `= ⊤`.

This is the mechanical shadow of Ruzsa's 1990 construction: the second moment of a genuine
additive basis of order 2 can be `O(N)`, so moment estimates cannot separate bounded from
unbounded representation functions. -/
theorem parity_and_moment_saturate_at_two :
    ∃ f : ℕ → ℕ, MomentAdmissible f ∧ ∀ n, f n ≤ 2 :=
  ⟨parityWitness,
   ⟨parityWitness_admissible.1, parityWitness_admissible.2, 4, parityWitness_moment⟩,
   parityWitness_le_two⟩

/-! ## What this campaign did NOT prove -/

/-- **The exact remaining obligation.**  Erdős 28 is the statement that `2` in
`two_le_limsup_of_basis` can be replaced by every natural number.  Kernel-checking that the
gap is exactly this is the honest terminal state of the campaign: the floor is `2`, the
target is `⊤`, and the published record (`≥ 8`, Borwein–Choi–Chu 2006) is NOT formalised
here. -/
theorem erdos28_iff_every_bound_exceeded :
    Erdos28Stmt ↔ ∀ (A : Set ℕ), IsBasis2 A → ∀ B : ℕ, ∃ n, B < rep A n := by
  constructor
  · intro H A hA B
    have h := (limsup_eq_top_iff A).mp (H A hA)
    by_contra hcon
    push_neg at hcon
    exact h ⟨B, fun n => hcon n⟩
  · intro H A hA
    rw [limsup_eq_top_iff]
    rintro ⟨B, hB⟩
    obtain ⟨n, hn⟩ := H A hA B
    have := hB n
    omega

end Erdos28
