import Mathlib

set_option autoImplicit false


-- Nontrivial 3-AP-free test: no a, a+d, a+2d all in A with d >= 1.
def is3APfree (A : List Nat) : Bool :=
  A.all (fun a => A.all (fun b =>
    let d := (b - a)
    b <= a || !(A.contains (b + d))))

-- All nonempty subsets of [1,N] as bitmasks, total and computable.
def subsets (N : Nat) : List (List Nat) :=
  (List.range (2^N)).map (fun m =>
    ((List.range N).filter (fun i => (m / 2^i) % 2 == 1)).map (· + 1))

def max3APfree (N : Nat) : Nat :=
  ((subsets N).filter is3APfree).foldl (fun acc s => max acc s.length) 0

-- FRAGMENT at N=5: L1 records r_3 values 4,4,5,6,11; at N=5 the claimed value is 4.
def check_r3_5 : Bool := max3APfree 5 == 4

def check_witness_5 : Bool :=
  is3APfree [1,2,4,5] && ([1,2,4,5].length == 4)

theorem msl_fmz_erdos3_campaign_001_R006_cert  : check_r3_5 = true ∧ check_witness_5 = true := by decide

-- axiom footprint
#print axioms is3APfree
#print axioms subsets
#print axioms max3APfree
#print axioms check_r3_5
#print axioms check_witness_5
#print axioms msl_fmz_erdos3_campaign_001_R006_cert
