/-
ERDOS902-F4-GE49-CANDIDATE-001

Formalisation target, not claimed compiled in this package.

The finite replay establishes the missing data layer.  To make f(4) >= 49 fully kernel-closed,
the remaining task is to formalise the external 37-class DRT(23) classification bridge (or
replace it by a direct exhaustive certificate), then connect the following generic argument
to Erdos902F4Step.

Target theorem shapes:

  theorem outside_deficit_le_12 ...
    : ∑ x in outN T v, (12 - ((inN T v) ∩ outN T x).card) ≤ 12

  theorem bad4_covered_by_outside_repairs ...
    : badCount H ≤ ∑ x in outN T v, repair (mask x)

  theorem admissible_repair_envelope_row35 ...
  theorem admissible_repair_envelope_row36 ...
    : repair ... W ≤ 66 + 72 * (12 - card W)

  theorem no_order_48 ...
    (hN : Fintype.card V = 48) (hS : HasSle T 4) : False

  theorem schutte_card_bound_four_49 (m : Nat) (h : SchutteAt 4 m) : 49 ≤ m

  theorem f_four_ge_49 : 49 ≤ f 4

The arithmetic endpoint is already present in Erdos902Capacity.envelope_arithmetic:
  24 * 66 + 72 * 12 = 2448
  2448 < 2475
  2448 < 2530
-/
