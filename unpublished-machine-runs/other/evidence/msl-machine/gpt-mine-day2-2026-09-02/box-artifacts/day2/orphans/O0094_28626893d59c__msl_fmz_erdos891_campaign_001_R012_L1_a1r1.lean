import Mathlib

set_option autoImplicit false


def P2 : Nat := 6
def P3 : Nat := 30
def Omega (m : Nat) : Nat :=
  (factors m).length
where
  factors : Nat -> List Nat
  | m => primeFactorsList m
-- Check: for every n in [P+1, P+bound], every multiple m of P with n <= m < n+P
-- satisfies m >= 2*P (hence Omega(m) = 1 + Omega(m/P) >= k+1 > k).
def checkWindow (P bound : Nat) : Bool :=
  (List.range bound).all fun i =>
    let n := P + 1 + i
    let ms := (List.range P).filterMap fun j =>
      let m := n + j
      if m % P == 0 then some m else none
    ms.all fun m => 2 * P <= m
-- Uniqueness sanity: at most one multiple of P in any half-open window of length P.
def checkUnique (P bound : Nat) : Bool :=
  (List.range bound).all fun i =>
    let n := P + 1 + i
    ((List.range P).filter (fun j => (n + j) % P == 0)).length <= 1

theorem msl_fmz_erdos891_campaign_001_R012_L1_a1r1  : checkWindow P2 500 = true ∧ checkUnique P2 500 = true ∧ checkWindow P3 500 = true ∧ checkUnique P3 500 = true := by decide

-- axiom footprint
#print axioms P2
#print axioms P3
#print axioms Omega
#print axioms checkWindow
#print axioms checkUnique
#print axioms msl_fmz_erdos891_campaign_001_R012_L1_a1r1
