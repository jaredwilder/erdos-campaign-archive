set_option autoImplicit false

def phi : Nat → Nat := fun n => (List.range (n+1)).filter (fun k => Nat.gcd k n = 1) |>.length  -- exact, Nat only, no floats
def leastPreimage (a : Nat) : Option Nat :=
  (List.range (a * a + 2)).find? (fun n => phi n = a)  -- φ(n) ≤ n, so any preimage of a lies below a+1 ≤ a*a+2
def sweep (N : Nat) : Bool :=
  ((List.range (N+1)).all (fun a =>
    match leastPreimage a with
    | none => true                     -- a ∉ im φ: nothing to check
    | some n => phi n = a))            -- exactness of the least-preimage map, integers only
def check : Bool := sweep 10000

theorem msl_fmz_erdos51_campaign_001_R008_L1  : check = true := by native_decide

#print axioms msl_fmz_erdos51_campaign_001_R008_L1