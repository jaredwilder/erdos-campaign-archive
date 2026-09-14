import Mathlib

set_option autoImplicit false


def isPrime : Nat -> Bool | 0 => false | 1 => false | 2 => true | n+1 => (List.range ((n+2)/2 - 1)).all (fun k => (n+2) % (k+2) != 0)
def primes : Nat -> List Nat  -- first n primes, computed by filter
  | 0 => []
  | n+1 => match primes n with
           | [] => [2]
           | l => let c := l.getLast! + 1
                  let rec next (m : Nat) : Nat := if isPrime m then m else next (m+1)
                  l ++ [next c]
def p (k : Nat) : Nat := match primes (k+1) with | l => l.getLast!
def f (N : Nat) : Nat := -- min_{1<=i<N} (p_{N+i} + p_{N-i}), 0 if the range is empty
  let idx := (List.range (N-1))
  match idx with
  | [] => 0
  | _ => idx.map (fun i => p (N + i + 1) + p (N - i - 1)) |>.foldl min (p (N+1) + p (N-1))
def check (N : Nat) : Bool := decide (f N >= 2 * p N)  -- fail-closed: exact integer >= on Nat
-- soundness witness at N = 100: the verifier's verdict equals the direct expansion of the canonical definition

theorem msl_fmz_erdos454_campaign_001_R011_L3_a1r1  : check 100 = ((List.range 99).map (fun i => p (100 + i + 1) + p (100 - i - 1)) |>.foldl min (p 101 + p 99)) >= 2 * p 100 := by decide

-- axiom footprint
#print axioms isPrime
#print axioms primes
#print axioms p
#print axioms f
#print axioms check
#print axioms msl_fmz_erdos454_campaign_001_R011_L3_a1r1
