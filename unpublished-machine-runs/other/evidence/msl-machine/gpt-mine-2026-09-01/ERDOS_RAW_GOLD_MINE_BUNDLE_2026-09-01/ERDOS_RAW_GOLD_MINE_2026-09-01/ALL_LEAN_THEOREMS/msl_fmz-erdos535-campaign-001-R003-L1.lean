set_option autoImplicit false

def sublists : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => let rest := sublists xs; rest ++ (rest.map (fun s => x :: s))

def tripleBad (a b c : Nat) : Bool :=
  a != b && b != c && a != c &&
  Nat.gcd a b == Nat.gcd a c && Nat.gcd a c == Nat.gcd b c

def admissible (s : List Nat) : Bool :=
  !(sublists s).any (fun t =>
    match t with
    | [a, b, c] => tripleBad a b c
    | _ => false)

def f3 (m : Nat) : Nat :=
  (sublists (List.range m |>.map (fun i => i + 1))).foldl
    (fun acc s => if admissible s then max acc s.length else acc) 0

def check_f3 : Bool :=
  [3, 4, 5, 6].map f3 == [2, 3, 3, 3]

theorem msl_fmz_erdos535_campaign_001_R003_L1  : check_f3 = true := by native_decide
