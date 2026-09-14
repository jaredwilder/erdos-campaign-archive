import Mathlib
set_option autoImplicit false
def witness : List Nat := [2, 4, 8, 16, 32, 64]
def isWitness (n : Nat) : Bool := (2 ^ n) % n == 0
def check : Bool := witness.all isWitness
namespace R008
/-- Decidable check of the full lemma content at a single s:
(1) exact valuation v₂(2^(2^s)) = 2^s, encoded as: 2^(2^s) ∣ 2^(2^s) and ¬(2^(2^s + 1) ∣ 2^(2^s));
(2) 2^s ≥ s;
(3) divisibility 2^s ∣ 2^(2^s) (witness family n = 2^s for k = 0). --/
def check_s (s : ℕ) : Bool :=
  (2 ^ (2 ^ s) ∣ 2 ^ (2 ^ s))
  && ¬ (2 ^ (2 ^ s + 1) ∣ 2 ^ (2 ^ s))
  && (s ≤ 2 ^ s)
  && ((2 ^ s : ℕ) ∣ 2 ^ (2 ^ s))
/-- Bounded check over s = 1, …, bound. --/
def check (bound : ℕ) : Bool :=
  (List.range bound).all (fun s => s = 0 || check_s s)
end R008
def witnessOk (a : Nat) : Bool := (2^(2^a)) % (2^a) == 0
def check_range : Bool := (List.range 7).all (fun a => witnessOk a)
set_option maxHeartbeats 400000

-- THE NORMALIZATION PRELUDE (msl_ladder, deterministic, $0).
-- The claim it tests: most leaf failures on an arithmetic DAG are SIDE-CONDITIONS
-- (an un-introduced hypothesis, a numeric coercion, a nonnegativity obligation),
-- not mathematics.  Each step is `try`, so the prelude never fails and never
-- changes what a tactic after it is allowed to prove.
macro "msl_prelude" : tactic =>
  `(tactic| ((try intros); (try push_cast); (try positivity)))

theorem erdos479_witness_family_all_s (s : ℕ) : ∀ (s : ℕ), (2 ^ (2 ^ s) ∣ 2 ^ (2 ^ s)) ∧ ¬(2 ^ (2 ^ s + 1) ∣ 2 ^ (2 ^ s)) ∧ (s ≤ 2 ^ s) ∧ ((2 ^ s : ℕ) ∣ 2 ^ (2 ^ s)) := by
  first
  | (decide; done)
  | (omega; done)
  | (norm_num; done)
  | (ring_nf; done)
  | (ring_nf; ring; done)
  | (linarith; done)
  | (nlinarith; done)
  | (positivity; done)
  | (gcongr; done)
  | (simp_all; done)
  | (aesop; done)
  | (msl_prelude; done)
  | (msl_prelude; omega; done)
  | (msl_prelude; norm_num; done)
  | (msl_prelude; linarith; done)
  | (msl_prelude; nlinarith; done)
  | (msl_prelude; ring_nf; done)
  | (msl_prelude; ring_nf; ring; done)
  | (msl_prelude; decide; done)
  | (msl_prelude; simp_all; done)
  | (msl_prelude; aesop; done)
  | (msl_prelude; field_simp; done)
  | (msl_prelude; field_simp; ring; done)
  | (msl_prelude; qify; omega; done)

#print axioms erdos479_witness_family_all_s
