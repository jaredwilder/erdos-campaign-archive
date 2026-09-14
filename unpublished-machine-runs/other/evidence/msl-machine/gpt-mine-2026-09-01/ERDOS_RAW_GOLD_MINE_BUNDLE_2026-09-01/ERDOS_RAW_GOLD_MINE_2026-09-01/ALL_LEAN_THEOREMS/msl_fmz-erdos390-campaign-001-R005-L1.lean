set_option autoImplicit false

inductive Verdict | PASS | FAIL | ABORT
deriving DecidableEq, Repr

-- Fail-closed verifier model: residual is either undefined (none) or defined (some).
def residualDefined : Option String → Bool
  | some _ => true
  | none   => false

def verify (residual : Option String) : Verdict :=
  if residualDefined residual then Verdict.PASS else Verdict.ABORT

-- Finite case check: over the two possible residual states (none / some s),
-- undefined residual never yields PASS and yields ABORT.
def caseNone : Bool := verify none ≠ Verdict.PASS ∧ verify none = Verdict.ABORT
def caseSome (s : String) : Bool :=
  verify (some s) = Verdict.PASS ∨ verify (some s) = Verdict.ABORT

def checkFailClosedFinite : Bool := caseNone ∧ caseSome "body"

theorem msl_fmz_erdos390_campaign_001_R005_L1  : checkFailClosedFinite = true := by decide
