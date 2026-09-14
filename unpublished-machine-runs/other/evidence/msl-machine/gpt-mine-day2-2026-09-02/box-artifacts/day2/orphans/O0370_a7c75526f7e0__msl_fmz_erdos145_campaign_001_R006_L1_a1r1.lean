import Mathlib

set_option autoImplicit false


def mu : Nat -> Int  -- Möbius function, computed by trial division over prime factors
  | n =>
    let rec go (m : Nat) (d : Nat) (cnt : Int) : Int :=
      if d * d > m then (if m > 1 then (if cnt + 1 % 2 == 0 then 1 else -1) * (if m > 1 && isSq m then 0 else 1) else if cnt % 2 == 0 then 1 else -1)
      else if m % d == 0 then
        if (m / d) % d == 0 then 0  -- squared prime factor
        else go (m / d) (d + 1) (cnt + 1)
      else go m (d + 1) cnt
    go n 2 0

def mobiusSum (X : Nat) (D : Nat) : Int :=
  (List.range (D + 1)).foldl (fun acc d => acc + mu d * ((X / d) : Int)) 0

def check_N : Bool :=
  mobiusSum 10000000 3162 == 6079271

theorem msl_fmz_erdos145_campaign_001_R006_L1_a1r1  : check_N = true := by native_decide

-- axiom footprint
#print axioms mu
#print axioms mobiusSum
#print axioms check_N
#print axioms msl_fmz_erdos145_campaign_001_R006_L1_a1r1
