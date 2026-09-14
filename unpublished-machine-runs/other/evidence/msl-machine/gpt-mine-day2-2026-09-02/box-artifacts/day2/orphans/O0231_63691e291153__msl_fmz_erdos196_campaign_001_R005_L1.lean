import Mathlib

set_option autoImplicit false



def perm : List Nat := [5, 3, 7, 1, 9, 8, 2, 6, 4]

def posOf (v : Nat) : Nat :=
  match perm.indexOf? v with | some i => i | none => 99

def noMonoAP : Bool :=
  ([1, 2].all fun d =>
    (List.range 9).all fun i =>
      let a := i + 1
      if a + 3 * d > 9 then true else
        let q := [posOf a, posOf (a + d), posOf (a + 2 * d), posOf (a + 3 * d)]
        !(q[0] < q[1] && q[1] < q[2] && q[2] < q[3]) &&
        !(q[0] > q[1] && q[1] > q[2] && q[2] > q[3]))

def check : Bool := noMonoAP && perm.Perm [1, 2, 3, 4, 5, 6, 7, 8, 9]

theorem msl_fmz_erdos196_campaign_001_R005_L1  : check = true := by decide

-- axiom footprint
#print axioms perm
#print axioms posOf
#print axioms noMonoAP
#print axioms check
#print axioms msl_fmz_erdos196_campaign_001_R005_L1
