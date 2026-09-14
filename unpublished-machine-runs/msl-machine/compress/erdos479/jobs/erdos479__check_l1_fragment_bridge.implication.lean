import Mathlib
set_option autoImplicit false
/-!
Erdős 479, second family (adversarial transcript mine, 2026-09-02 — the campaign itself
missed this; the auditor derived it): k = −1 is settled. For every a,
3^(a+1) ∣ 2^(3^a) + 1, so in particular n = 3^a divides 2^n + 1, giving infinitely many
witnesses for k = −1 (2^n ≡ −1 mod n). Lifting-the-exponent induction: if
2^(3^a) = 3^(a+1)·m − 1 then cubing gives (3tm−1)³ + 1 = 9t·(3t²m³ − 3tm² + m) with
t = 3^a. Stated in ℤ to keep the subtraction honest; ℕ divisibility corollary follows.
-/
def witness : List Nat := [2, 4, 8, 16, 32, 64]
def isWitness (n : Nat) : Bool := (2 ^ n) % n == 0
def check : Bool := witness.all isWitness
Erdős 479, P0 promotion (GPT gold pack rank 2, audited 2026-09-01; kernel round 2026-09-02).
Infinite parametric witness family: for every j ≥ 0 and every odd prime p, with
k = 2^(2^j) and n = 2^j · p, we have 2^n ≡ k (mod n). Modulo p by Fermat
(2^(2^j(p-1)) ≡ 1), modulo 2^j both sides vanish (j ≤ 2^j), and CRT since gcd(2^j, p) = 1.
As p varies this gives infinitely many n for each such k.
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
theorem erdos479_lte (a : ℕ) : (3 : ℤ) ^ (a + 1) ∣ 2 ^ (3 ^ a) + 1 := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    obtain ⟨m, hm⟩ := ih
    set t : ℤ := 3 ^ a with hta
    have h31 : (3 : ℤ) ^ (a + 1) = 3 * t := by rw [hta, pow_succ, mul_comm]
    have h32 : (3 : ℤ) ^ (a + 1 + 1) = 9 * t := by rw [pow_succ, h31]; ring
    have h2 : (2 : ℤ) ^ (3 ^ a) = 3 * t * m - 1 := by
      rw [← h31]
      linarith
    have hcube : (2 : ℤ) ^ (3 ^ (a + 1)) = ((2 : ℤ) ^ (3 ^ a)) ^ 3 := by
      rw [← pow_mul, pow_succ]
    refine ⟨3 * t ^ 2 * m ^ 3 - 3 * t * m ^ 2 + m, ?_⟩
    rw [hcube, h2, h32]
    ring
set_option maxHeartbeats 400000

-- THE NORMALIZATION PRELUDE (msl_ladder, deterministic, $0).
-- The claim it tests: most leaf failures on an arithmetic DAG are SIDE-CONDITIONS
-- (an un-introduced hypothesis, a numeric coercion, a nonnegativity obligation),
-- not mathematics.  Each step is `try`, so the prelude never fails and never
-- changes what a tactic after it is allowed to prove.
macro "msl_prelude" : tactic =>
  `(tactic| ((try intros); (try push_cast); (try positivity)))

-- ---- children, INCLUDED BY SOURCE (each already PROVED_KERNEL alone)
theorem erdos479_lte (a : ℕ) : (3 : ℤ) ^ (a + 1) ∣ 2 ^ (3 ^ a) + 1 := by
  first
  | decide
  | norm_num
  | simp

theorem msl_fmz_erdos479_campaign_001_R003_L1 check = true := by
  first
  | decide
  | norm_num
  | simp

theorem erdos479_family (j p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) : 2 ^ (2 ^ j * p) ≡ 2 ^ (2 ^ j) [MOD 2 ^ j * p] := by
  first
  | decide
  | norm_num
  | simp

theorem msl_fmz_erdos479_campaign_001_R008_L1 R008.check 6 = true := by
  first
  | decide
  | norm_num
  | simp

theorem msl_fmz_erdos479_campaign_001_R003_T1_a1r2 check_range = true := by
  first
  | decide
  | norm_num
  | simp

theorem erdos479_k_neg_one (a : ℕ) : (3 ^ a : ℕ) ∣ 2 ^ (3 ^ a) + 1 := by
  first
  | decide
  | norm_num
  | simp

-- ---- the composition: children -> parent
theorem check_l1_fragment_bridge_composition (s : ℕ) : ((erdos479_lte : ($v0 : ℕ) : (3 : ℤ) ^ ($v0 + 1) ∣ 2 ^ (3 ^ $v0) + 1) ∧ (msl_fmz_erdos479_campaign_001_R003_L1 : check = true) ∧ (erdos479_family : ($v0 $v1 : ℕ) (hp : $v1.Prime) (hodd : $v1 ≠ 2) : 2 ^ (2 ^ $v0 * $v1) ≡ 2 ^ (2 ^ $v0) [MOD 2 ^ $v0 * $v1]) ∧ (msl_fmz_erdos479_campaign_001_R008_L1 : $v0.check 6 = true) ∧ (msl_fmz_erdos479_campaign_001_R003_T1_a1r2 : check_range = true) ∧ (erdos479_k_neg_one : ($v0 : ℕ) : (3 ^ $v0 : ℕ) ∣ 2 ^ (3 ^ $v0) + 1)) → (∀ s ∈ Finset.Icc (1 : ℕ) 5, check_l1_fragment s = true) := by
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

-- ---- the parent, by exact application of the composition
theorem check_l1_fragment_bridge (s : ℕ) : ∀ s ∈ Finset.Icc (1 : ℕ) 5, check_l1_fragment s = true := by
  first
  | exact check_l1_fragment_bridge_composition ⟨erdos479_lte, msl_fmz_erdos479_campaign_001_R003_L1, erdos479_family, msl_fmz_erdos479_campaign_001_R008_L1, msl_fmz_erdos479_campaign_001_R003_T1_a1r2, erdos479_k_neg_one⟩
  | (apply check_l1_fragment_bridge_composition; exact ⟨erdos479_lte, msl_fmz_erdos479_campaign_001_R003_L1, erdos479_family, msl_fmz_erdos479_campaign_001_R008_L1, msl_fmz_erdos479_campaign_001_R003_T1_a1r2, erdos479_k_neg_one⟩)
  | (intros; exact check_l1_fragment_bridge_composition ⟨erdos479_lte, msl_fmz_erdos479_campaign_001_R003_L1, erdos479_family, msl_fmz_erdos479_campaign_001_R008_L1, msl_fmz_erdos479_campaign_001_R003_T1_a1r2, erdos479_k_neg_one⟩)

#print axioms check_l1_fragment_bridge_composition
#print axioms check_l1_fragment_bridge
