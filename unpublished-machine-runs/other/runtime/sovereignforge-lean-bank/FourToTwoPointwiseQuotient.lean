/- Exhaustive structural obstruction for pointwise colour quotients.
   Scope: four abstract colour labels mapped independently to Bool.
   This does not rule out nonlocal recolouring constructions. -/
def collision (a b c d : Bool) : Bool :=
  (a == b) || (a == c) || (a == d) || (b == c) || (b == d) || (c == d)

theorem every_pointwise_four_to_two_map_collides (a b c d : Bool) :
    collision a b c d = true := by
  revert a b c d
  decide
