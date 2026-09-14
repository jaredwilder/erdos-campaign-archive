import Mathlib

set_option autoImplicit false


def sumsCover (x : Nat) (L : List Nat) : Bool :=
  L.any (fun a => L.any (fun b => a + b = x))

def nextFree (L : List Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | n, f+1 => if sumsCover L n then nextFree L (n+1) f else n

def build (L : List Nat) (x : Nat) : Nat → Nat → List Nat
  | _, 0 => L
  | k+1, f+1 =>
    let y := nextFree L x f
    build (L ++ [y]) (y+1) k f

def A1 : List Nat := build [1] 2 40 400

def check_l1 : Bool :=
  (A1.length = 41) ∧
  (A1.getD 0 0 = 1) ∧
  ((List.range 40).all (fun i =>
      A1.getD (i+1) 0 - A1.getD i 0 = 2)) ∧
  ((List.range 41).all (fun i => A1.getD i 0 = 2*i + 1))

theorem msl_fmz_erdos341_campaign_001_R003_L1_a3r2  : check_l1 = true := by decide

-- axiom footprint
#print axioms sumsCover
#print axioms nextFree
#print axioms build
#print axioms A1
#print axioms check_l1
#print axioms msl_fmz_erdos341_campaign_001_R003_L1_a3r2
