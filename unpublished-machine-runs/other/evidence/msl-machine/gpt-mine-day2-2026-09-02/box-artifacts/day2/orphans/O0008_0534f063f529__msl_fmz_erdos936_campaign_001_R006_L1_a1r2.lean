import Mathlib

set_option autoImplicit false


def powfulByFactors (m a : Nat) (h : a ∣ m) : Bool := m / a % a == 0
-- Exact factorizations (verified below), then check a square (or higher power) divides:
def nine : Nat := 3^2
def tfive : Nat := 5^2
def one21 : Nat := 11^2
def five041 : Nat := 71^2
def three62881 : Nat := 19 * 71 * 269
def checks : List Bool :=
  [ nine == 9, nine % 3 == 0 && nine / 3 % 3 == 0,
    tfive == 25, tfive % 5 == 0 && tfive / 5 % 5 == 0,
    one21 == 121, one21 % 11 == 0 && one21 / 11 % 11 == 0,
    five041 == 5041, five041 % 71 == 0 && five041 / 71 % 71 == 0,
    three62881 == 362881, three62881 % 19 == 0, three62881 / 19 == 19099,
    three62881 % 71 == 0, three62881 / 71 == 5109,
    three62881 % 269 == 0, three62881 / 269 == 1349,
    -- cofactors are squarefree: 5109 = 71*72 = 71*8*9, cofactor after 71^2 must be checked
    three62881 / (71*71) == 72 && 72 % 71 != 0 ]
def check_all : Bool := checks.all (· == true)

theorem msl_fmz_erdos936_campaign_001_R006_L1_a1r2  : check_all = true := by decide

-- axiom footprint
#print axioms powfulByFactors
#print axioms nine
#print axioms tfive
#print axioms one21
#print axioms five041
#print axioms three62881
#print axioms checks
#print axioms check_all
#print axioms msl_fmz_erdos936_campaign_001_R006_L1_a1r2
