import Mathlib
set_option autoImplicit false
/-!
Erdős 479, P0 promotion (GPT gold pack rank 2, audited 2026-09-01; kernel round 2026-09-02).
Infinite parametric witness family: for every j ≥ 0 and every odd prime p, with
k = 2^(2^j) and n = 2^j · p, we have 2^n ≡ k (mod n). Modulo p by Fermat
(2^(2^j(p-1)) ≡ 1), modulo 2^j both sides vanish (j ≤ 2^j), and CRT since gcd(2^j, p) = 1.
As p varies this gives infinitely many n for each such k.
-/
set_option maxHeartbeats 400000

-- THE NORMALIZATION PRELUDE (msl_ladder, deterministic, $0).
-- The claim it tests: most leaf failures on an arithmetic DAG are SIDE-CONDITIONS
-- (an un-introduced hypothesis, a numeric coercion, a nonnegativity obligation),
-- not mathematics.  Each step is `try`, so the prelude never fails and never
-- changes what a tactic after it is allowed to prove.
macro "msl_prelude" : tactic =>
  `(tactic| ((try intros); (try push_cast); (try positivity)))

theorem erdos479_family_odd_generalized (j : ℕ) (m : ℕ) (hm1 : 1 ≤ j) (hodd : Odd m) : theorem erdos479_family_odd_generalized (j m : ℕ) (hm1 : 1 ≤ j) (hodd : Odd m) :
    (2 ^ (2 ^ j * m) : ℤ) ≡ (2 ^ (2 ^ j) : ℤ) [ZMOD ((2 ^ j * m : ℕ) : ℤ)] := by
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

#print axioms erdos479_family_odd_generalized
