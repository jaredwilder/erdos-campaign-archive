/-
  blade_ast_extract.lean -- the METAPROGRAM-GRADE side of `blades_ast.py`.

  ⛔ WHY THIS FILE EXISTS. Section 4.2 of BLADES-STANDARD-v1.0 says, in as many words:
  "Use Lean metaprogramming / environment inspection, NOT REGEX, for binder use, declaration
  dependencies, reducible unfolding, theorem AST, and #print axioms closure." A surface parser
  cannot see through `abbrev`, through notation, through instance arguments, or through a binder
  that is used only after delta-reduction -- so a surface parser that reports "no unused binder"
  is reporting that IT found none, which is a different sentence.

  `blades_ast.py` therefore ships a static fallback that marks every clean verdict
  BLOCKED_INCONCLUSIVE and stamps `"method": "STATIC_FALLBACK_DEGRADED"` on its evidence. This
  file is what removes the asterisk. Feed its output back with:

      lake env lean oracle/frontier_formalizer/blade_ast_extract.lean > ast.json     # integrator
      python oracle/frontier_formalizer/blades_ast.py --lean F.lean --ast-json ast.json

  ⛔ THIS FILE HAS NEVER BEEN COMPILED BY THE AGENT THAT WROTE IT. `blades_ast.py` does not run
  Lean -- the resident kernel is a machine-wide singleton and P0-A does not own it. Anything
  derived from this file is metaprogram-grade ONLY once the integrator has actually run it and
  the run is receipted. Until then `blades_ast.py` must keep saying DEGRADED, and it does: the
  upgrade is gated on the presence of a parsed `--ast-json`, never on the existence of this text.

  HOW TO POINT IT AT A TARGET. Replace the `import` line's module with the artifact under audit
  (or `import Mathlib` and `#eval! BladeAstExtract.dump` inside the artifact itself). The extractor
  reads `env.constants.map₂` -- the extension map -- which holds EXACTLY the declarations this
  module added, never the ~200k inherited from Mathlib. That is the whole reason no name filter,
  no prefix guess, and no line-range heuristic appears below.
-/
import Lean

open Lean Elab Command Meta

namespace BladeAstExtract

/-- Binder-by-binder occupancy of a declaration's TYPE.

    `b.hasLooseBVar 0` is the property the standard actually asks for: after the binder is
    introduced, does the body still mention it? This is decided on the elaborated `Expr`, so
    notation, coercions and instance arguments are already resolved -- which is precisely what
    the regex fallback cannot do. -/
partial def binderUse : Expr → Array (Name × Bool) → Array (Name × Bool)
  | .forallE n _ b _, acc => binderUse b (acc.push (n, b.hasLooseBVar 0))
  | .lam n _ b _, acc     => binderUse b (acc.push (n, b.hasLooseBVar 0))
  | _, acc                => acc

/-- DEEP unused-binder collector, with the binder's PARENT HEAD attached. Measured need,
    2026-08-31: the name-only version fired on ten FAITHFUL_OPEN survivors, and every fire
    but one was the hypothesis binder of `dite`/`ite` (`if h : P then ...`) or a structure
    field's `self` - legitimate style, not a defect. #165's genuine class is a comprehension
    binder (`setOf`/`sInf`) whose non-use collapses the object. Only the parent context can
    tell these apart, so each entry is "binderName@parentHead" where parentHead is the head
    constant the lambda is an argument of (or `_root_` at the spine). The consumer decides
    which parents convict; this file only reports. -/
partial def deepUnused : Expr -> String -> Array String -> Array String
  | .lam n _ b _, parent, acc =>
    let acc := if b.hasLooseBVar 0 then acc else acc.push (n.toString ++ "@" ++ parent)
    deepUnused b parent acc
  | .forallE n _ b _, parent, acc =>
    let acc := if b.hasLooseBVar 0 then acc else acc.push (n.toString ++ "@" ++ parent)
    deepUnused b parent acc
  | .app f a, parent, acc =>
    -- the ARGUMENT's parent is this application's head; the function part keeps ours
    let head := (Expr.app f a).getAppFn
    let headName := match head with
      | .const c _ => c.toString
      | _ => parent
    deepUnused a headName (deepUnused f parent acc)
  | .letE _ t v b _, parent, acc =>
    deepUnused b parent (deepUnused v parent (deepUnused t parent acc))
  | .mdata _ e, parent, acc => deepUnused e parent acc
  | .proj _ _ e, parent, acc => deepUnused e parent acc
  | _, _, acc => acc

/-- Every constant this module DECLARED (not imported). `map₂` is the extension map. -/
def ownDecls (env : Environment) : Array Name :=
  env.constants.map₂.foldl (init := #[]) fun acc n _ =>
    if n.isInternal || n.isImplementationDetail then acc else acc.push n

/-- The declaration-dependency edge set: which own-constants a declaration's type+value mention.
    B29 (dead source content) and B28 (witness-path coverage) are reachability questions on
    exactly this graph, and answering them on the elaborated value is the difference between
    "the identifier does not appear in the file text" and "the theorem does not depend on it". -/
def depsOf (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let fromType := ci.type.getUsedConstants
    let fromVal := match ci.value? with
      | some v => v.getUsedConstants
      | none => #[]
    (fromType ++ fromVal).filter fun m => (env.constants.map₂.contains m) && m != n

/-- The trust boundary: `#print axioms` as data. `sorryAx` appearing here is what separates a
    sorried conjecture from a closed proof, and B31 (not owned by P0-A) consumes it. -/
def axiomsOf (n : Name) : CommandElabM (Array Name) := do
  -- `Lean.collectAxioms` is this toolchain's spelling (probed via batchd:
  -- `CollectAxioms.collect`/`.State` are not exported names here)
  liftTermElabM (collectAxioms n)

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.thmInfo _)   => "theorem"
  | some (.defnInfo _)  => "def"
  | some (.axiomInfo _) => "axiom"
  | some (.opaqueInfo _) => "opaque"
  | some (.inductInfo _) => "inductive"
  | some (.ctorInfo _)  => "ctor"
  | some (.recInfo _)   => "rec"
  | some (.quotInfo _)  => "quot"
  | none                => "unknown"

/-- Emit the whole summary as one JSON object on stdout. Schema is pinned so
    `blades_ast.py` refuses an output it does not recognise rather than half-reading it. -/
def dump : CommandElabM Unit := do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for n in ownDecls env do
    let ci := (env.find? n).get!
    -- ⛔ WHICH EXPRESSION CARRIES THE BINDER QUESTION differs by kind, and getting this
    -- wrong makes every plain function read as all-unused (a non-dependent arrow never
    -- mentions its binder in the TYPE). For a def, B05's question is about the VALUE:
    -- #165's dead binder is unused in the defining SET, not in `ℕ → ℕ`. For a theorem,
    -- the STATEMENT (type) is the object under audit; its proof term is irrelevant here.
    let subject := match ci with
      | .defnInfo d => d.value
      | _           => ci.type
    let binders := (binderUse subject #[]).map fun (bn, used) =>
      Json.mkObj [("name", Json.str bn.toString), ("used_in_body", Json.bool used)]
    let ax ← axiomsOf n
    let ty ← liftTermElabM do
      return toString (← Meta.ppExpr ci.type)
    decls := decls.push <| Json.mkObj [
      ("name", Json.str n.toString),
      ("kind", Json.str (kindOf env n)),
      ("type", Json.str ty),
      ("binders", Json.arr binders),
      ("nested_unused", Json.arr ((match ci with
        | .defnInfo d => deepUnused d.value "_root_" #[]
        | _ => #[]).map Json.str)),
      ("deps", Json.arr ((depsOf env n).map fun m => Json.str m.toString)),
      ("axioms", Json.arr (ax.map fun m => Json.str m.toString))]
  let out := Json.mkObj [
    ("schema", Json.str "oracle.frontier-formalizer.blade-ast-extract.v1"),
    ("declarations", Json.arr decls)]
  logInfo out.compress

end BladeAstExtract

-- ⛔ The integrator runs THIS line. It prints one JSON object and nothing else that matters;
-- `blades_ast.py --ast-json` scans for the first `{"schema":"...blade-ast-extract.v1"...}`.
#eval! BladeAstExtract.dump
