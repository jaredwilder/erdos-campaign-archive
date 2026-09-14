import Mathlib

set_option autoImplicit false


def F : Nat := 7
def g : Nat := 3
-- g is a primitive root mod 7: its powers 3^0..3^5 mod 7 are 1,3,2,6,4,5.
def powG (a : Nat) : Nat := (3^(a%6)) % 7
-- Bose–Chowla elements: g^a - g mod 7
def bcSet : List Nat := (List.range 6).map (fun a => (powG a + 7 - 3) % 7)
-- multiset equality on length-2 lists via erase-cancelation
def multisetEq (u v : List Nat) : Bool :=
  (u.foldr (fun x acc => acc.erase x) v).isEmpty && (v.foldr (fun x acc => acc.erase x) u).isEmpty
def checkQuad : Nat -> Nat -> Nat -> Nat -> Bool
  | b1, b2, b3, b4 =>
    if powG (b1+b2) == powG (b3+b4) then
      multisetEq [b1%6, b2%6] [b3%6, b4%6]
    else true
def checkAll : Bool :=
  (List.range 6).all (fun b1 =>
   (List.range 6).all (fun b2 =>
    (List.range 6).all (fun b3 =>
     (List.range 6).all (fun b4 => checkQuad b1 b2 b3 b4))))
def checkDistinct : Bool := (bcSet.eraseDups).length == bcSet.length

theorem msl_fmz_erdos158_campaign_001_R002_L1  : checkAll = true && checkDistinct = true := by decide

-- axiom footprint
#print axioms F
#print axioms g
#print axioms powG
#print axioms bcSet
#print axioms multisetEq
#print axioms checkQuad
#print axioms checkAll
#print axioms checkDistinct
#print axioms msl_fmz_erdos158_campaign_001_R002_L1
