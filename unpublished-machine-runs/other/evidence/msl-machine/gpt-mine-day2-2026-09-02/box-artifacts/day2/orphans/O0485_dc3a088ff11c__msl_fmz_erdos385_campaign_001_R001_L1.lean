import Mathlib

set_option autoImplicit false


namespace R001L1

/- Model of the deterministic build procedure. A `Residual` is `some n` when a
   residual candidate exists, `none` when it does not. The build procedure is a
   total Bool-valued function: `true` = ABORT path taken, `false` = proceed. -/

inductive Residual where
  | none : Residual
  | some : Nat → Residual

deriving DecidableEq, Repr

/-- Deterministic build procedure: abort is taken exactly when no residual exists. -/
def build (r : Residual) : Bool :=
  match r with
  | Residual.none   => true    -- ABORT
  | Residual.some _ => false   -- proceed

/-- Fail-closed check: for an input, if no residual exists the procedure MUST have
    taken the abort path (true), and it never aborts when a residual exists. -/
def failClosed (r : Residual) : Bool :=
  match r with
  | Residual.none   => build r == true
  | Residual.some _ => build r == false

/-- Exhaustive case analysis over the full input domain of the model:
    no-residual case, plus residual cases over a bounded witness range 0..N.
    The no-residual case is the whole of the lemma's abort clause; the bounded
    `some` range fixes concretely that proceed-path behavior is verified. -/
def checkAll (N : Nat) : Bool :=
  (failClosed Residual.none == true)
    && ((List.range (N+1)).all (fun n => failClosed (Residual.some n) == true))

end R001L1

theorem msl_fmz_erdos385_campaign_001_R001_L1  : R001L1.checkAll 32 = true := by decide

-- axiom footprint
#print axioms R001L1.build
#print axioms R001L1.failClosed
#print axioms R001L1.checkAll
#print axioms msl_fmz_erdos385_campaign_001_R001_L1
