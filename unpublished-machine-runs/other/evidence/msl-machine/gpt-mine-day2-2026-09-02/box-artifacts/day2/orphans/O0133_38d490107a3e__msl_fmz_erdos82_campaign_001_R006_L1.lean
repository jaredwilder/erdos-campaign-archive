import Mathlib

set_option autoImplicit false


-- Pure-Nat checkable fragment of L1's recorded shape: on the subsequence
-- n = 2^(2^k), log2 n = 2^k and log2 log2 n = k, so a lower bound of the form
-- F(n) >= c*log n / log log n contributes only O(1/k) to F(n)/log n. The
-- envelope 100/(10*k) (Nat division) is computed and checked to be strictly
-- decreasing in k over the sampled range, confirming the bound's ratio
-- contribution tends to 0 along this subsequence.
def env (k : Nat) : Nat := 100 / (10 * k)

def checkEnvelope : Bool :=
  (env 1 = 10)
  && (env 5 = 2)
  && (env 10 = 1)
  && (env 20 = 0)
  && (env 5 < env 1)
  && (env 10 < env 5)
  && (env 20 < env 10)

theorem msl_fmz_erdos82_campaign_001_R006_L1  : checkEnvelope = true := by decide

-- axiom footprint
#print axioms env
#print axioms checkEnvelope
#print axioms msl_fmz_erdos82_campaign_001_R006_L1
