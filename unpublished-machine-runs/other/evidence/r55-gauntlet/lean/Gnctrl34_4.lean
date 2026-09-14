/-!
# `gnctrl_34_4` — the non-vacuity control for the R(3,4) INDEPENDENCE nest, standalone

Audit 10 (`oracle/evidence/r55-gauntlet/audit10.log`) found that the control generator emitted
one `gnctrl_*` per block, keyed on the CLIQUE size, so a block whose two nests differ in depth
left the second nest uncontrolled. `gn_34_4` — the depth-4 nest that `not_sufficesN_34` feeds
`n34` to, via `gh_34_4n` — was that nest.

This file re-establishes the missing control on its own, with NO imports and NO Mathlib, so a
stranger can check it without reading the 1,421-line `R55Final.lean`. The definition block below
is copied VERBATIM from `R55Final.lean` (`S34`/`a34`/`n34` at lines 1316-1320, `gn_34_4` at
lines 1349-1352); the theorems match the sibling pattern exactly
(`gnctrl_33_3` line 1290, `gnctrl_34_3` line 1372, `gnctrl_24_4` line 1143, `gnctrl_44_4` line 1151).

⛔ What a control buys. A nest that cannot return `false` proves nothing, however cleanly the
kernel accepts `gn_34_4 n34 = true`. The two theorems below are the two directions on the SAME
routine: it says `true` on the witness's complement colouring, and `false` on the complete graph
(where `[0,1,2,3]` is an independent 4-set of `n34`'s argument, so the nest MUST fail).

Replay: `lake env lean Gnctrl34_4.lean` on Lean 4 v4.31.0-rc1. Imports nothing.
-/

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 200000000

/-! ## The definition block, VERBATIM from `R55Final.lean` -/

def S34 : List Nat := [1, 4, 7]

def a34 (i j : Nat) : Bool := S34.contains ((i % 8 + 8 - j % 8) % 8)

def n34 (i j : Nat) : Bool := ! a34 i j

def gn_34_4 (e : Nat → Nat → Bool) : Bool :=
  (List.range 8).all fun a => (List.range 8).all fun b => (! (a < b)) || (! e a b) ||
      ((List.range 8).all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      ((List.range 8).all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d)))

/-! ## The two directions of the same nest -/

/-- the POSITIVE side, verbatim from `R55Final.lean` line 1370: the nest returns `true` on the
    complement of the order-8 circulant, i.e. `Cay(Z_8, ±{1,4})` has no independent 4-set. -/
theorem gh_34_4n : gn_34_4 n34 = true := by decide

/-- ⭐ THE MISSING CONTROL. The same nest returns `false` on the constant-`true` colouring, where
    an independent 4-set plainly exists — so `gh_34_4n` above is a real exhaustion and not a
    predicate that says `true` to everything. Exactly the pattern of `gnctrl_34_3`. -/
theorem gnctrl_34_4 : gn_34_4 (fun _ _ => true) = false := by decide

#print axioms gh_34_4n
#print axioms gnctrl_34_4
