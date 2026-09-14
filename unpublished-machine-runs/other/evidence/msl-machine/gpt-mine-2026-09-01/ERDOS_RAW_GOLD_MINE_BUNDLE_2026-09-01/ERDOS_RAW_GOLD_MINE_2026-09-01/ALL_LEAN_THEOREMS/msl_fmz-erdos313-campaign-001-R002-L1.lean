set_option autoImplicit false

def binom : Nat → Nat → Nat
  | 0, 0 => 1 | 0, _+1 => 0 | _+1, 0 => 1
  | n+1, k+1 => binom n k + binom n (k+1)

def rowSum (n : Nat) : Nat :=
  (List.range (n+1)).foldl (fun acc k => acc + binom n k) 0

def pow2 : Nat → Nat
  | 0 => 1 | n+1 => 2 * pow2 n

def checkOne (n : Nat) : Bool := rowSum n == pow2 n

def checkAll : Nat → Bool
  | 0 => checkOne 0
  | n+1 => checkAll n && checkOne (n+1)

def check_L1 : Bool := checkAll 20

theorem msl_fmz_erdos313_campaign_001_R002_L1  : check_L1 = true := by decide
