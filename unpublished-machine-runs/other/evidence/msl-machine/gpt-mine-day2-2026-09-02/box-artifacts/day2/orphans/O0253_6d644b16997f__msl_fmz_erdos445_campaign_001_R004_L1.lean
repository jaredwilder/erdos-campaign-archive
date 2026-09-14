import Mathlib

set_option autoImplicit false


def powMod : Nat → Nat → Nat → Nat
  | _, 0, m => 1 % m
  | b, k+1, m => (b * powMod b k m) % m

/-- Strict-open window (n, n + 5^(51/100)) with 5^(51/100) ≈ 2.698 < 3:
    admissible a,b are exactly n+1 and n+2. -/
def winP5 (n : Nat) : Bool :=
  (List.range 2).any fun da =>
    (List.range 2).any fun db =>
      let a := n + 1 + da
      let b := n + 1 + db
      (a * b) % 5 == 1

def scanP5 : Bool := (List.range 6).all winP5

/-- ord_7(2) = 3 exactly: 2^3 ≡ 1 (mod 7), and neither 2^1 nor 2^2 is. -/
def ord7_2 : Bool :=
  powMod 2 3 7 == 1 && powMod 2 1 7 != 1 && powMod 2 2 7 != 1

theorem msl_fmz_erdos445_campaign_001_R004_L1  : ord7_2 = true && scanP5 = true := by decide

-- axiom footprint
#print axioms powMod
#print axioms winP5
#print axioms scanP5
#print axioms ord7_2
#print axioms msl_fmz_erdos445_campaign_001_R004_L1
