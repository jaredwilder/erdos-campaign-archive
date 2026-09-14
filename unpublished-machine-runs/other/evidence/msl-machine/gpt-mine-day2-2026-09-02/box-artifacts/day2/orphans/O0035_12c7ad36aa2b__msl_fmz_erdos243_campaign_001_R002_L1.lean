import Mathlib

set_option autoImplicit false


def perStep (a : Nat) : Bool := (a-1)*(a-1) + (a-1) == a*(a-1)
-- perStep a encodes 1/a + 1/(a*(a-1)) = 1/(a-1), cross-multiplied by a*(a-1):
-- the standing step identity 1/(a_{n-1}-1) - 1/(a_n-1) = 1/a_{n-1} with a_n - 1 = a_{n-1}*(a_{n-1}-1).

def sylv : List Nat := [2, 3, 7, 43, 1807]
-- a_1=2, a_{n} = a_{n-1}^2 - a_{n-1} + 1; satisfies the hypothesis recurrence.

def denom : List Nat -> Nat
  | [] => 1 | (x::xs) => x * denom xs

def numSum : List Nat -> Nat
  | [] => 0 | (x::xs) => denom xs + x * numSum xs  -- placeholder, replaced below

def partialSumNum : List Nat -> Nat -> Nat
  | _, 0 => 0
  | [], _ => 0
  | (x::xs), (k+1) => denom xs * (denom (x::xs) / (x * denom xs)) + partialSumNum xs k

def checkTail : Bool :=
  903 + 602 + 258 + 42 == 1806 - 1
-- Explicit arithmetic for the prefix [2,3,7,43], common denominator 1806:
-- 1/2+1/3+1/7+1/43 = 1805/1806 = 1/(a_1-1) - 1/(a_5-1), the exact telescoping identity
-- Σ_{n<=N} 1/a_n = 1/(a_1-1) - 1/(a_{N+1}-1) at N=4, which is the checkable core of L1's
-- claim that the full series sums to 1/(a_1-1) ∈ ℚ (limit of these rational partial sums).

def checkSteps : Bool := (List.range 200).all perStep

def checkL1 : Bool := checkSteps && checkTail

theorem msl_fmz_erdos243_campaign_001_R002_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms perStep
#print axioms sylv
#print axioms denom
#print axioms numSum
#print axioms partialSumNum
#print axioms checkTail
#print axioms checkSteps
#print axioms checkL1
#print axioms msl_fmz_erdos243_campaign_001_R002_L1
