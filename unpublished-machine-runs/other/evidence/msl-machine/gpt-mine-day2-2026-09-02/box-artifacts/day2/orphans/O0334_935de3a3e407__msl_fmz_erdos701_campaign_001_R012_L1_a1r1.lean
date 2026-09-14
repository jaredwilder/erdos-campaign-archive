import Mathlib

set_option autoImplicit false


def pow : List Nat → List (List Nat)
  | [] => [[]]
  | a::as => let p := pow as; p ++ (p.map (fun s => a::s))

def allSets : List Nat := [0,1,2,3]  -- masks for ∅,{1},{2},{1,2}

def subTab : Nat → List Nat
  | 0 => [0] | 1 => [0,1] | 2 => [0,2] | 3 => [0,1,2,3] | _ => []

def hered (F : List Nat) : Bool := F.all (fun m => (subTab m).all F.elem)

def inter (F : List Nat) : Bool :=  -- all-pairs incl. A=B; ∅ (mask 0) can never be a member
  F.all (fun a => F.all (fun b => a &&& b != 0))

def maxInter (F : List Nat) : Nat :=
  (pow F).filter inter |>.map (fun s => s.length) |>.foldl max 0

def star (F : List Nat) (bit : Nat) : Nat :=
  F.countP (fun m => m &&& bit != 0)  -- bit=1 for x={1}, bit=2 for x={2}

def downsets : List (List Nat) := (pow allSets).filter hered

def check : Bool :=
  downsets.length == 6 &&
  downsets.all (fun F => maxInter F ≤ max (star F 1) (star F 2))

theorem msl_fmz_erdos701_campaign_001_R012_L1_a1r1  : check = true := by decide

-- axiom footprint
#print axioms pow
#print axioms allSets
#print axioms subTab
#print axioms hered
#print axioms inter
#print axioms maxInter
#print axioms star
#print axioms downsets
#print axioms check
#print axioms msl_fmz_erdos701_campaign_001_R012_L1_a1r1
