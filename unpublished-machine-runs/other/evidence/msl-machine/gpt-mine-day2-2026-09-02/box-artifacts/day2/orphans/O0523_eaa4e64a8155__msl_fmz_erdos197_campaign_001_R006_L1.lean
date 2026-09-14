import Mathlib

set_option autoImplicit false


def W1 : List Nat := [1,5,3,7,2,6,4,8]
def W2 : List Nat := [7,2,4,8,3,6,1,5]

def IsPerm (w : List Nat) : Bool :=
  w.length = 8 && (List.range 8).all (fun n => w.elem (n+1)) && w.all (fun v => 1 <= v && v <= 8)

-- no i < j < k with w[i],w[j],w[k] in arithmetic progression (order-sensitive)
def NoPosAP (w : List Nat) : Bool :=
  (List.range w.length).all (fun i =>
   (List.range w.length).all (fun j =>
    (List.range w.length).all (fun k =>
     !(i < j && j < k && 2 * (w.getD j 0) = w.getD i 0 + w.getD k 0))))

-- no three positions forming an AP whose values also form an AP (set-to-set)
def NoSetAP (w : List Nat) : Bool :=
  (List.range w.length).all (fun i =>
   (List.range w.length).all (fun j =>
    (List.range w.length).all (fun k =>
     !(i < k && i + k = 2 * j && 2 * (w.getD j 0) = w.getD i 0 + w.getD k 0))))

def check_witnesses : Bool :=
  IsPerm W1 && IsPerm W2 && NoPosAP W1 && NoSetAP W2

theorem msl_fmz_erdos197_campaign_001_R006_L1  : check_witnesses = true := by decide

-- axiom footprint
#print axioms W1
#print axioms W2
#print axioms IsPerm
#print axioms NoPosAP
#print axioms NoSetAP
#print axioms check_witnesses
#print axioms msl_fmz_erdos197_campaign_001_R006_L1
