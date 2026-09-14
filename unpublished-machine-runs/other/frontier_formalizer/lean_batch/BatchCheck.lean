/-
BatchCheck: elaborate MANY independent Lean files against ONE preloaded Mathlib environment.

⛔ WHY THIS EXISTS. Spawning `lake env lean` per file pays the `import Mathlib` cost every time.
Measured on this machine: minutes per file, hours for a corpus of 248. A previous attempt to fix
that by putting many artifacts in one compile unit was WRONG in a way that mattered: files shared
a unit and inherited each other's failures, producing a fake 89% pass rate and reporting a file
as FAILED in 0.24s that a single-file compile returned VERIFIED in 18.7s.

    speed came from sharing a compile unit. correctness required not sharing one.

Lean's `Environment` is persistent and immutable, which dissolves that tradeoff. Import Mathlib
ONCE, then elaborate each file starting from that same base environment. Each file gets a fresh
`Command.State` built from `baseEnv`, so a declaration or an error in one file CANNOT be visible
to the next. Isolation is by construction, not by discipline.

⛔ THE FILE'S OWN `import` LINES ARE PARSED AND DISCARDED. `Parser.parseHeader` returns a parser
state positioned after the header; we continue from there against `baseEnv`. Feeding the import
line to `processCommands` would raise "invalid import command", which is itself one of the errors
in our failure census.

⛔ THIS REPORTS ELABORATION, NOT PROOF. A file whose theorems are closed with `sorry` elaborates
with zero ERRORS and emits a `declaration uses 'sorry'` WARNING. Those are different questions and
this tool keeps them apart: `errors` counts only `MessageSeverity.error`, and `sorries` counts the
sorry warnings separately.
-/
import Lean

open Lean Elab

-- Char literals with backslash escapes tripped the parser; compare code points instead.
def escape (s : String) : String :=
  s.foldl (fun acc c =>
    if c.toNat == 34 then acc ++ "\\\""
    else if c.toNat == 92 then acc ++ "\\\\"
    else if c.toNat == 10 then acc ++ "\\n"
    else if c.toNat < 32 then acc ++ " "
    else acc.push c) ""

unsafe def checkOne (baseEnv : Environment) (path : String) : IO Unit := do
  let content ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext content path
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  -- Fresh command state from the SHARED base environment: isolation by construction.
  let cmdState := Command.mkState baseEnv messages {}
  let s ← IO.processCommands inputCtx parserState cmdState
  let msgs := s.commandState.messages.toList
  let mut errs : Array String := #[]
  let mut sorries : Nat := 0
  for m in msgs do
    let txt ← m.data.toString
    let pos := m.pos
    if m.severity == MessageSeverity.error then
      errs := errs.push s!"{pos.line}:{pos.column}: {txt}"
    else if (txt.splitOn "declaration uses 'sorry'").length > 1 then
      sorries := sorries + 1
  let body := String.intercalate "," (errs.toList.map (fun e => "\"" ++ escape e ++ "\""))
  IO.println s!"\{\"file\":\"{escape path}\",\"errors\":{errs.size},\"sorries\":{sorries},\"messages\":[{body}]}"
  (← IO.getStdout).flush

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let listFile := args.head!
  let paths := (← IO.FS.readFile listFile).splitOn "\n"
    |>.map String.trim |>.filter (fun s => s != "")
  IO.eprintln s!"[BatchCheck] importing Mathlib once for {paths.length} files..."
  let t0 ← IO.monoMsNow
  -- ⛔ WITHOUT THIS THE ENVIRONMENT IS A TRAP. `importModules` loads the .oleans but does NOT
  -- run their `initialize` blocks unless initializer execution is enabled. Those blocks register
  -- instances, attributes and elaborators. Measured: without it, `def f : Nat := 1` fails with
  -- "type class instance expected OfNat Nat 1" - an obviously-fine file looks broken, and every
  -- verdict downstream is garbage while looking perfectly well-formed.
  Lean.enableInitializersExecution
  let baseEnv ← importModules #[{ module := `Mathlib }] {} (trustLevel := 1024)
  let t1 ← IO.monoMsNow
  IO.eprintln s!"[BatchCheck] Mathlib loaded in {t1 - t0} ms"
  for p in paths do
    try
      checkOne baseEnv p
    catch e =>
      IO.println s!"\{\"file\":\"{escape p}\",\"errors\":-1,\"sorries\":0,\"messages\":[\"{escape (toString e)}\"]}"
  let t2 ← IO.monoMsNow
  IO.eprintln s!"[BatchCheck] {paths.length} files in {t2 - t1} ms ({(t2-t1) / (max 1 paths.length)} ms/file)"
