import Mathlib

set_option autoImplicit false


def isMono (m : Nat) (a b c : Nat) : Bool :=
  ((m >>> a) % 2 == (m >>> b) % 2) && ((m >>> b) % 2 == (m >>> c) % 2)

def aps9 : List (Nat × Nat × Nat) :=
  [(0,1,2),(1,2,3),(2,3,4),(3,4,5),(4,5,6),(5,6,7),(6,7,8),
   (0,2,4),(1,3,5),(2,4,6),(3,5,7),(4,6,8),
   (0,3,6),(1,4,7),(2,5,8),(0,4,8)]

def aps8 : List (Nat × Nat × Nat) :=
  [(0,1,2),(1,2,3),(2,3,4),(3,4,5),(4,5,6),(5,6,7),
   (0,2,4),(1,3,5),(2,4,6),(3,5,7),
   (0,3,6),(1,4,7)]

def avoids (m : Nat) (aps : List (Nat × Nat × Nat)) : Bool :=
  aps.all (fun t => !(isMono m t.1 t.2.1 t.2.2))

def W23check : Bool :=
  (List.range 512).all (fun m => !avoids m aps9) &&
  (List.range 256).any (fun m => avoids m aps8)

theorem msl_fmz_erdos197_campaign_001_R004_L1  : W23check = true := by native_decide

-- axiom footprint
#print axioms isMono
#print axioms aps9
#print axioms aps8
#print axioms avoids
#print axioms W23check
#print axioms msl_fmz_erdos197_campaign_001_R004_L1
