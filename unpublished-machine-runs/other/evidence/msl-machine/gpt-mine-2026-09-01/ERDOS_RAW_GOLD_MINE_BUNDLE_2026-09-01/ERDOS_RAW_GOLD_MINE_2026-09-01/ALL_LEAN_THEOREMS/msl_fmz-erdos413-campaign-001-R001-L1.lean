set_option autoImplicit false

-- Fragment of L1, kernel-decidable: finite grid {0..7}, canonical
-- <=-threshold family B_eps := (t <= eps) with t = 3. Membership transfer
-- is computed with if-then-else on Bool (no implication in Bool context).
-- The check verifies, for every pair eps1 <= eps2 on the grid, that
-- membership in B_{eps1} transfers to membership in B_{eps2} — the exact
-- transitivity clause of L1, finitized. Total, computable, Nat/Bool only.

def Bfamily (t eps : Nat) : Bool := t <= eps

def transfer (b : Nat -> Bool) (eps1 eps2 : Nat) : Bool :=
  if b eps1 then b eps2 else true

def pairOK (b : Nat -> Bool) (eps1 eps2 : Nat) : Bool :=
  if eps1 <= eps2 then transfer b eps1 eps2 else true

def allPairsOK (b : Nat -> Bool) (n : Nat) : Bool :=
  loop1 b n n
where
  loop1 (b : Nat -> Bool) (n : Nat) : Nat -> Bool
    | 0 => true
    | (i+1) => loop2 b n n i && loop1 b n i
where
  loop2 (b : Nat -> Bool) (n : Nat) (i : Nat) : Nat -> Bool
    | 0 => true
    | (j+1) => pairOK b i j && loop2 b n i j

def check_L1 : Bool :=
  allPairsOK (Bfamily 3) 8

theorem msl_fmz_erdos413_campaign_001_R001_L1  : check_L1 = true := by decide
