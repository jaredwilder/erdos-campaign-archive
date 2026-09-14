import Mathlib

set_option autoImplicit false


-- Model of the fail-closed verifier's sign-resolution rule.
-- g is 'pinned' when an evaluator is present; here g is UNPINNED, so the
-- totient-preimage count is unavailable and every integer test on it must
-- abort rather than silently pass or fail.

def GValue : Type := Option Nat            -- none = unpinned / unresolved sign

def g_pinned : GValue := none              -- packet inspection: no evaluator on file

def testLe (m n : Nat) : Bool := m * m <= n        -- g(n)^2 <= n  (shape only)
def testLe9 (m n : Nat) : Bool := m^10 <= n^9      -- g(n)^10 <= n^9 (shape only)

/-- Fail-closed verifier: any test touching an unpinned g ABORTS (false);
    it never returns true, and never silently instantiates g. --/
def verifier_verdict (gv : GValue) (n : Nat) : Bool :=
  match gv with
  | none => false                          -- abort on unresolved sign
  | some m => testLe m n && testLe9 m n

/-- The checkable content of L1: with g unpinned (g_pinned = none), the integer
    tests g(n)^2<=n and g(n)^10<=n^9 are uninstantiable and certificate scope is
    empty — the verifier's verdict is abort (false) for every n in a sampled range. --/
def check_fail_closed (range_hi : Nat) : Bool :=
  (verifier_verdict g_pinned 1 == false)
  && (List.all (List.range range_hi) (fun n => verifier_verdict g_pinned (n+1) == false))
  && (verifier_verdict (some 0) 1 == true)   -- sanity: a pinned g DOES resolve (fail-closed is not vacuous)
  && (verifier_verdict (some 0) 2 == true)

theorem msl_fmz_erdos821_campaign_001_R008_L1  : check_fail_closed 64 = true := by decide

-- axiom footprint
#print axioms GValue
#print axioms g_pinned
#print axioms testLe
#print axioms testLe9
#print axioms verifier_verdict
#print axioms check_fail_closed
#print axioms msl_fmz_erdos821_campaign_001_R008_L1
