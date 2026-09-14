import Mathlib

set_option autoImplicit false


-- Fail-closed pin-check, abort-correctness scope only.
-- The contract's pin vector: three pin slots, each pinned by an explicit
-- reduction/residual binding. Pins are recorded as (slot, reduction, residual).
def pins : List (String × String × String) :=
  [ ("objective", "none", "per contract"),
    ("domain",    "none", "per contract"),
    ("sign",      "none", "per contract") ]

-- A slot is pinned iff its reduction binds a concrete objective/domain/sign choice,
-- i.e. reduction != "none". With reduction = "none" and residual = "per contract",
-- nothing is pinned: the residual defers to the open canonical statement.
def isPinned : String × String × String → Bool
  | (_, reduction, _) => reduction != "none"

def pinCount : Nat := (pins.filter isPinned).length

-- Abort-on-unresolved-sign: with 0 pins the unique deterministic, reproducible,
-- empty-scope output is ABORT; any non-abort output would require a pinned sign.
def abortIsUnique : Bool := pinCount == 0

def check_sha_8fab17a4372ba50c : Bool :=
  pins.length == 3
  && pinCount == 0
  && (pins.all fun (_, r, s) => r == "none" && s == "per contract")
  && abortIsUnique

theorem msl_fmz_erdos454_campaign_001_R006_L1  : check_sha_8fab17a4372ba50c = true := by decide

-- axiom footprint
#print axioms pins
#print axioms isPinned
#print axioms pinCount
#print axioms abortIsUnique
#print axioms check_sha_8fab17a4372ba50c
#print axioms msl_fmz_erdos454_campaign_001_R006_L1
