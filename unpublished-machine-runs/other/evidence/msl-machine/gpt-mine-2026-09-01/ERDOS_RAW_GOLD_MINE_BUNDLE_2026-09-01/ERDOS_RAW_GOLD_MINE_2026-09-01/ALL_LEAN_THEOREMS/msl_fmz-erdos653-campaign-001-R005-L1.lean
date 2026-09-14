set_option autoImplicit false

def dedupList : List Nat → List Nat
  | [] => []
  | x :: xs => let r := dedupList xs; if r.contains x then r else x :: r

def cls (n : Nat) : List Nat :=
  (List.range (n - 1)).map (fun k => min (k + 1) (n - (k + 1)))

def check (n : Nat) : Bool :=
  (dedupList (cls n)).length == n / 2

def checkAll (m : Nat) : Bool :=
  (List.range m).all (fun i => check (i + 3))

theorem msl_fmz_erdos653_campaign_001_R005_L1  : checkAll 40 = true := by native_decide
