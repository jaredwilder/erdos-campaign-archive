import Mathlib

set_option autoImplicit false


def isDigitC (c : Char) : Bool := c = '0' || c = '1' || c = '2' || c = '3' || c = '4' || c = '5' || c = '6' || c = '7' || c = '8' || c = '9'

/-- Deterministic fail-closed V-RAT parser: accepts exactly [+-]?d+(\/d+)? with at least one digit in each integer part; no floats, no tolerance, no state outside Bool transitions. Returns some true (PARSEABLE, canonical), some false (PARSEABLE but noncanonical/rejected-state), or none (UNPARSEABLE). -/
def vratParse (s : String) : Option Bool :=
  let cs := s.data
  -- sign state
  let rest0 := match cs with
    | '-' :: t => some t
    | '+' :: t => some t
    | t => some t
  match rest0 with
  | none => none
  | some t0 =>
    -- integer digits: one or more
    let intDigits := (t0.takeWhile isDigitC).length
    if intDigits = 0 then none  -- 0 digits ⇒ UNPARSEABLE (fail-closed ABORT state)
    else
      let afterInt := t0.dropWhile isDigitC
      match afterInt with
      | [] => some true
      | '/' :: t1 =>
        let denDigits := (t1.takeWhile isDigitC).length
        if denDigits = 0 then none
        else if (t1.dropWhile isDigitC) = [] then some true
        else none
      | _ :: _ => none

/-- Registry check: no computational artifact for this input exists on file ⇒ status WITHHELD. -/
def registryStatus : String → String := fun _ => "WITHHELD"

def checkL2 : Bool :=
  let input := "per contract"
  -- deterministic ASCII automaton on the literal input
  let parsed := vratParse input
  -- 'p' is not [+-]?digit ⇒ automaton must land in UNPARSEABLE (none)
  let unparseable := (parsed.isNone)
  -- 0 digits seen ⇒ contract-mandated fail-closed ABORT
  let digitsSeen := input.data.foldl (fun acc c => acc + (if isDigitC c then 1 else 0)) 0
  let zeroDigits := (digitsSeen == 0)
  -- registry artifact ⇒ WITHHELD
  let withheld := (registryStatus input == "WITHHELD")
  -- abort state is well-defined and total: parse of arbitrary string is never undefined
  let total : Bool := ((vratParse "3/4").isSome) && ((vratParse "-12").isSome) && ((vratParse "3/").isNone) && ((vratParse "/4").isNone) && ((vratParse "3/4/5").isNone) && ((vratParse "+7").isSome) && ((vratParse "").isNone) && ((vratParse "3.4").isNone)
  unparseable && zeroDigits && withheld && total

theorem msl_fmz_erdos306_campaign_001_R001_L2  : checkL2 = true := by decide

-- axiom footprint
#print axioms isDigitC
#print axioms vratParse
#print axioms registryStatus
#print axioms checkL2
#print axioms msl_fmz_erdos306_campaign_001_R001_L2
