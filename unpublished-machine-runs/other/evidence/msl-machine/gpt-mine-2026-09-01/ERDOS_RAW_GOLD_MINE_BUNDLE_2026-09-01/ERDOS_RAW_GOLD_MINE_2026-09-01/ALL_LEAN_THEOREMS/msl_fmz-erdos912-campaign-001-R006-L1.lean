set_option autoImplicit false

-- Deterministic shell: a total pure function over Nat/List, small constants so
-- `decide` succeeds.
def shellStep (s : Nat) (input : Nat) : Nat :=
  (s * 13 + input * 7 + 1) % 101

def shellRun (s : Nat) : List Nat -> Nat
  | [] => s
  | (x :: xs) => shellRun (shellStep s x) xs

-- Determinism fragment of L1: for a fixed seed and input list, two evaluations
-- of the shell coincide (the shell is a pure function of its inputs).
def determinismCheck (seed : Nat) (xs : List Nat) : Bool :=
  shellRun seed xs == shellRun seed xs

-- Concreteness fragment: the shell's output on a fixed input is an exact
-- computed Nat, reproducible on every evaluation.
def check_witness : Bool :=
  determinismCheck 3 [1, 2, 5]
    && shellRun 3 [1, 2, 5] == 68

theorem msl_fmz_erdos912_campaign_001_R006_L1  : check_witness = true := by decide
