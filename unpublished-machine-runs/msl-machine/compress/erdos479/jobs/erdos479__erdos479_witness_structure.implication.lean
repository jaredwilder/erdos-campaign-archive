import Mathlib
set_option autoImplicit false
/-!
Erdős 479, P0 promotion (GPT gold pack rank 2, audited 2026-09-01; kernel round 2026-09-02).
Infinite parametric witness family: for every j ≥ 0 and every odd prime p, with
k = 2^(2^j) and n = 2^j · p, we have 2^n ≡ k (mod n). Modulo p by Fermat
(2^(2^j(p-1)) ≡ 1), modulo 2^j both sides vanish (j ≤ 2^j), and CRT since gcd(2^j, p) = 1.
As p varies this gives infinitely many n for each such k.
-/
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
set_option maxHeartbeats 400000

-- THE NORMALIZATION PRELUDE (msl_ladder, deterministic, $0).
-- The claim it tests: most leaf failures on an arithmetic DAG are SIDE-CONDITIONS
-- (an un-introduced hypothesis, a numeric coercion, a nonnegativity obligation),
-- not mathematics.  Each step is `try`, so the prelude never fails and never
-- changes what a tactic after it is allowed to prove.
macro "msl_prelude" : tactic =>
  `(tactic| ((try intros); (try push_cast); (try positivity)))

-- ---- children, INCLUDED BY SOURCE (each already PROVED_KERNEL alone)
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

-- ---- the composition: children -> parent
theorem erdos479_witness_structure_composition (j : ℕ) (n : ℕ) (hj : 2 ^ j ≤ n) (h : (2 ^ n : ℕ) ≡ 2 ^ (2 ^ j) [MOD n]) : ((erdos479_family : ($v0 $v1 : ℕ) (hp : $v1.Prime) (hodd : $v1 ≠ 2) : 2 ^ (2 ^ $v0 * $v1) ≡ 2 ^ (2 ^ $v0) [MOD 2 ^ $v0 * $v1]) ∧ (msl_fmz_erdos479_campaign_001_R008_L1 : $v0.check 6 = true)) → (theorem erdos479_witness_structure (j n : ℕ) (hj : 2 ^ j ≤ n)
    (h : (2 ^ n : ℕ) ≡ 2 ^ (2 ^ j) [MOD n]) :
    (2 ^ (2 ^ j) : ℕ) * (2 ^ (n - 2 ^ j) - 1) ≡ 0 [MOD n] ∧
    n.factorization 2 ≤ 2 ^ j) := by
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
theorem erdos479_witness_structure (j : ℕ) (n : ℕ) (hj : 2 ^ j ≤ n) (h : (2 ^ n : ℕ) ≡ 2 ^ (2 ^ j) [MOD n]) : theorem erdos479_witness_structure (j n : ℕ) (hj : 2 ^ j ≤ n)
    (h : (2 ^ n : ℕ) ≡ 2 ^ (2 ^ j) [MOD n]) :
    (2 ^ (2 ^ j) : ℕ) * (2 ^ (n - 2 ^ j) - 1) ≡ 0 [MOD n] ∧
    n.factorization 2 ≤ 2 ^ j := by
  first
  | exact erdos479_witness_structure_composition ⟨erdos479_family, msl_fmz_erdos479_campaign_001_R008_L1⟩
  | (apply erdos479_witness_structure_composition; exact ⟨erdos479_family, msl_fmz_erdos479_campaign_001_R008_L1⟩)
  | (intros; exact erdos479_witness_structure_composition ⟨erdos479_family, msl_fmz_erdos479_campaign_001_R008_L1⟩)

#print axioms erdos479_witness_structure_composition
#print axioms erdos479_witness_structure
