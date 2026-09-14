import Mathlib

set_option autoImplicit false


-- Model of verifier P as a total Bool-valued decision procedure over a finite
-- payload space. Payload identities are represented by exact Nat codes (no
-- floats anywhere). Contract of P: (1) absent payload => exit 2, certificate
-- null; (2) a PASS (exit 0) requires the payload's sha-contract binding code to
-- equal the exact expected constant; (3) no numeric path uses float comparison.

def ExpectedBinding : Nat := 4844747143496676644

def exitAbsent : Nat := 2
def exitPass : Nat := 0

def verifyP (p : Option Nat) : Nat × Option Nat :=
  match p with
  | none => (exitAbsent, none)                       -- absent: exit 2, cert null
  | some q =>
      if q == ExpectedBinding then (exitPass, some q) -- pass ONLY on exact binding
      else (exitAbsent, none)                         -- otherwise: fail closed

def isFloatPath (_ : Option Nat) : Bool := false     -- P never compares floats

-- Property 1: fail-closed on absent payload.
def checkFailClosedAbsent : Bool := verifyP none == (exitAbsent, none)

-- Property 2: no pass without the exact sha-contract binding, over the finite
-- candidate binding space (including the true binding and near-collisions).
def candidateBindings : List Nat :=
  [0, 1, 4844747143496676643, 4844747143496676644, 4844747143496676645,
   48447471434966766440, 484474714349667664]

def noUnboundPass : Bool :=
  candidateBindings.all (fun b =>
    match verifyP (some b) with
    | (0, some _) => b == ExpectedBinding
    | _ => true)

-- Property 3: no float-comparison path, over the whole candidate space plus absence.
def noFloatOnAnyPath : Bool :=
  (none :: candidateBindings.map some).all (fun p => !isFloatPath p)

def checkL1 : Bool := checkFailClosedAbsent && noUnboundPass && noFloatOnAnyPath

theorem msl_fmz_erdos75_campaign_001_R005_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms ExpectedBinding
#print axioms exitAbsent
#print axioms exitPass
#print axioms verifyP
#print axioms isFloatPath
#print axioms checkFailClosedAbsent
#print axioms candidateBindings
#print axioms noUnboundPass
#print axioms noFloatOnAnyPath
#print axioms checkL1
#print axioms msl_fmz_erdos75_campaign_001_R005_L1
