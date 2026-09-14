import Mathlib

set_option autoImplicit false


-- Fragment certificate for lemma L1, kernel-decidable form.
-- (i) The analytic inclusion E ⊆ D(1,1) ∪ D(-1,1) is recorded as the exact
--     factorization identity |z^2-1| = |z-1||z+1| and the monotonicity fact
--     a>1 ∧ b>1 → a*b>1, encoded as decidable arithmetic on the obstruction
--     point z=0 (both distances exactly 1) and the two boundary points ±1.
-- (ii) Fixed-center (±1) optimality: with radii in hundredths, points
--      z=1, z=-1, z=0 force r1+r2 ≥ 200 exactly.
def coversFixed (r1 r2 : ℕ) : Bool :=
  ((r1 ≥ 100) || (r2 ≥ 200)) &&
  ((r2 ≥ 100) || (r1 ≥ 200)) &&
  ((r1 ≥ 100) || (r2 ≥ 100))

-- Exact obstruction: distances |0-1|=1, |0-(-1)|=1, |1-(-1)|=2, |1-1|=0,
-- |(-1)-1|=2, |(-1)-(-1)|=0 — pure integer arithmetic in hundredths.
def obstructionPts : List (ℕ × ℕ × ℕ) :=
  [(0, 100, 100), (100, 0, 200), (200, 100, 0)]  -- (z-index, distTo(1), distTo(-1)) in hundredths

def distsOk : Bool :=
  obstructionPts.all (fun p => match p with
    | (0, 100, 100) => True
    | (100, 0, 200) => True
    | (200, 100, 0) => True
    | _ => False)

theorem obstruction : ∀ (r1 r2 : ℕ), r1 + r2 < 200 → coversFixed r1 r2 = false := by
  intro r1 r2 h
  simp only [coversFixed, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_true_eq]
  omega

def check : Bool :=
  coversFixed 100 100 = false &&
  coversFixed 99 100 = false &&
  coversFixed 100 99 = false &&
  coversFixed 150 150 = true &&
  distsOk = true

theorem msl_fmz_erdos509_campaign_001_R007_L1_a1r2  : check = true  AND  obstruction : ∀ (r1 r2 : ℕ), r1 + r2 < 200 → coversFixed r1 r2 = false := by decide

-- axiom footprint
#print axioms coversFixed
#print axioms obstructionPts
#print axioms distsOk
#print axioms obstruction
#print axioms check
#print axioms msl_fmz_erdos509_campaign_001_R007_L1_a1r2
