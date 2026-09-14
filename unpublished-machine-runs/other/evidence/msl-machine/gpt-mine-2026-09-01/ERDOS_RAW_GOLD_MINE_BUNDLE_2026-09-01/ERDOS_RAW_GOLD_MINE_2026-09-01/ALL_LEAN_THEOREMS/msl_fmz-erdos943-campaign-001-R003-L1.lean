set_option autoImplicit false

def isPow (n : Nat) : Bool :=
  n ≤ 1 ∨ ((List.range (n+1)).all fun p =>
    p = 0 ∨ n % p ≠ 0 ∨ p * p ∣ n)

def repCount (n : Nat) : Nat :=
  ((List.range (n+1)).filter fun d =>
    n % d = 0 ∧ isPow d ∧ isPow (n / d)).length

def checkRange (bound : Nat) : Bool :=
  (List.range (bound+1)).all fun n =>
    n ≤ 1 ∨ ¬ isPow n ∨ repCount n ≤ 2 * Nat.sqrt n

theorem msl_fmz_erdos943_campaign_001_R003_L1  : checkRange 300 = true ∧ repCount 8 = 2 ∧ repCount 72 = 6 := by decide
