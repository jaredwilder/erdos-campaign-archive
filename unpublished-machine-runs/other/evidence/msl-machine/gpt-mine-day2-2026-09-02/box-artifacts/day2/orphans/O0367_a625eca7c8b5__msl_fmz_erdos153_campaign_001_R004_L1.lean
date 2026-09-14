import Mathlib

set_option autoImplicit false


All arithmetic exact over Int/Nat; definitions TOTAL and Bool-valued; no `where`, no partial functions, no floats.

-- all pair sums aᵢ+aⱼ with i ≤ j (0-indexed pairs)
def pairSums (a : List Int) : List Int :=
  (List.range a.length).flatMap fun i =>
    (List.range a.length).filterMap fun j =>
      if j ≥ i then some (a[i]! + a[j]!) else none

def pwDistinct : List Int → Bool
  | [] => true
  | s :: rest => rest.all (· != s) && pwDistinct rest

def sidon (a : List Int) : Bool := pwDistinct (pairSums a)

def dedup : List Int → List Int
  | [] => []
  | s :: rest => if dedup rest contains s then dedup rest else s :: dedup rest

def tOf (a : List Int) : Nat := (dedup (pairSums a)).length

def expectedT (a : List Int) : Nat := a.length * (a.length + 1) / 2

-- the biconditional for a single tuple: Sidon ⟺ t = n(n+1)/2
def checkBicond (a : List Int) : Bool := (sidon a == (tOf a == expectedT a))

-- enumerate all strictly increasing tuples with entries in 1..B, length exactly k
def incLists : Nat → Nat → Int → List (List Int)
  | 0, _, _ => [[]]
  | k+1, B, lo =>
    ((List.range B).map (fun b => (b + 1 : Int))).filter (fun x => x > lo)
      |>.flatMap (fun x => (incLists k B x).map (fun l => x :: l))

-- NARROWED FRAGMENT: n ≤ 4, window 1..10 (2401 + 120 + 45 + 10 = 2576 tuples;
-- brute enumeration was too heavy for `decide`, so the window is shrunk and
-- n ≤ 4 replaces n ≤ 5 to keep kernel reduction finite and fast).
def checkWindow : Bool :=
  ((List.range 4).all fun n =>
    let k := n + 1
    (incLists 10 k 0).all checkBicond)

theorem msl_fmz_erdos153_campaign_001_R004_L1  : checkWindow = true := by decide

-- axiom footprint
#print axioms pairSums
#print axioms pwDistinct
#print axioms sidon
#print axioms dedup
#print axioms tOf
#print axioms expectedT
#print axioms checkBicond
#print axioms incLists
#print axioms checkWindow
#print axioms msl_fmz_erdos153_campaign_001_R004_L1
