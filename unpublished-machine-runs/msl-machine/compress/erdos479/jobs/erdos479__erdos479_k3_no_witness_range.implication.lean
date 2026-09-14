import Mathlib
set_option autoImplicit false
def witness : List Nat := [2, 4, 8, 16, 32, 64]
def isWitness (n : Nat) : Bool := (2 ^ n) % n == 0
def check : Bool := witness.all isWitness
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

-- ---- children, INCLUDED BY SOURCE (each already PROVED_KERNEL alone)
theorem msl_fmz_erdos479_campaign_001_R003_L1 check = true := by
  first
  | decide
  | norm_num
  | simp

theorem msl_fmz_erdos479_campaign_001_R003_T1_a1r2 check_range = true := by
  first
  | decide
  | norm_num
  | simp

-- ---- the composition: children -> parent
theorem erdos479_k3_no_witness_range_composition : ((msl_fmz_erdos479_campaign_001_R003_L1 : check = true) ∧ (msl_fmz_erdos479_campaign_001_R003_T1_a1r2 : check_range = true)) → (theorem erdos479_k3_no_witness_range : ∀ n ∈ Finset.Icc (1 : ℕ) 120, (2 ^ n : ℕ) % n ≠ 3) := by
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
theorem erdos479_k3_no_witness_range : theorem erdos479_k3_no_witness_range : ∀ n ∈ Finset.Icc (1 : ℕ) 120, (2 ^ n : ℕ) % n ≠ 3 := by
  first
  | exact erdos479_k3_no_witness_range_composition ⟨msl_fmz_erdos479_campaign_001_R003_L1, msl_fmz_erdos479_campaign_001_R003_T1_a1r2⟩
  | (apply erdos479_k3_no_witness_range_composition; exact ⟨msl_fmz_erdos479_campaign_001_R003_L1, msl_fmz_erdos479_campaign_001_R003_T1_a1r2⟩)
  | (intros; exact erdos479_k3_no_witness_range_composition ⟨msl_fmz_erdos479_campaign_001_R003_L1, msl_fmz_erdos479_campaign_001_R003_T1_a1r2⟩)

#print axioms erdos479_k3_no_witness_range_composition
#print axioms erdos479_k3_no_witness_range
