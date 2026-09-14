/-
BatchServer: a RESIDENT Lean elaborator. Import Mathlib ONCE, then elaborate an unbounded
stream of independent snippets against that one environment, each in its own `Command.State`.

⛔ WHY THIS EXISTS, WITH THE NUMBERS.
  * `import Mathlib` costs 108 s cold, per process. 248 files = 7.4 hours of pure import.
  * A resident `lean --server` driven over LSP (oracle/frontier_formalizer/lean_daemon.py)
    got that to 35 s/file. Better; still dominated by per-request server bookkeeping.
  * Sharing ONE compile unit across files was tried and is WRONG: files inherited each
    other's failures, producing a fake 89% pass rate, and a file that a single-file compile
    returned VERIFIED in 18.7 s was reported FAILED in 0.24 s.
        speed came from sharing a compile unit; correctness required not sharing one.
  Lean's `Environment` is persistent and immutable, which dissolves the tradeoff: every
  snippet forks a FRESH `Command.State` off the same `baseEnv`, so a declaration or an error
  in one snippet cannot be visible to the next. Isolation is by construction, not discipline.

⛔ THE `lean_exe` HYPOTHESIS WAS REFUTED. RECORD IT HONESTLY.
  The predecessor (lean_batch/BatchCheck.lean) ran INTERPRETED (`lake env lean --run`) and
  `def f : Nat := 1` failed with "type class instance expected: OfNat Nat 1". The standing
  hypothesis was that instance/attribute/elaborator registration rides on module
  initializers that only wire up in a COMPILED binary, so building it as a Lake `lean_exe`
  would fix it. Built as a `lean_exe` (supportInterpreter := true), it failed IDENTICALLY.
  Toggling `enableInitializersExecution` changed nothing either way. Compiling was NOT the
  fix.

  THE ACTUAL CAUSE was `importModules #[`Mathlib]` being called by hand. That environment
  passes every direct probe - 10,737 modules, `instOfNatNat` present, "+" present in the
  token table, `term` category present - and still elaborates as if nothing were imported:
      def f : Nat := 1                    -> type class instance expected: OfNat Nat 1
      theorem t : (1:Nat) + 1 = 2         -> unexpected token '+'; expected ':=' ...
      noncomputable def g : R := Real.pi  -> Real.pi has type Real, expected type R
  The last one is the tell: the notation for the reals was silently AUTO-BOUND as an
  implicit variable, i.e. no imported notation was in scope at all. `Lean.Elab.processHeader`
  - the path `lean` itself uses to finalize a header - fixed all eleven selftest cases in
  one change.

  A GREEN DIRECT PROBE IS NOT A WORKING ENVIRONMENT. Everything we could ask the environment
  about said yes while elaboration said no. Only end-to-end elaboration of a known-good
  snippet distinguishes the two, which is why `--selftest` asserts on SNIPPETS.
  `supportInterpreter := true` is still required in the lakefile - Mathlib tactic code is IR
  in the .oleans and is executed at elaboration time - it just was not the missing piece.

⛔ THIS REPORTS ELABORATION, NOT PROOF. A snippet closed with `sorry` elaborates with zero
  errors and emits a `declaration uses 'sorry'` warning. Those are different questions, so
  `errors` counts only `MessageSeverity.error` and `sorries` is counted separately.

WIRE PROTOCOL (stdin/stdout, line framed, byte-counted so snippets may contain anything):
    -> "LEN <n>\n" followed by exactly <n> bytes of UTF-8 Lean source
    <- one JSON line: {"ok":bool,"errors":[...],"n_errors":N,"sorries":N,"ms":N}
    -> "QUIT\n"  terminates.
  A byte count, not a sentinel string, because a Lean snippet can legally contain any line
  we might have chosen as a sentinel.
-/
import Lean

open Lean Elab

/-- JSON string escaping. Compare code points: char literals with backslash escapes tripped
    the parser in the predecessor file. -/
def escape (s : String) : String :=
  s.foldl (fun acc c =>
    if c.toNat == 34 then acc ++ "\\\""
    else if c.toNat == 92 then acc ++ "\\\\"
    else if c.toNat == 10 then acc ++ "\\n"
    else if c.toNat == 13 then acc ++ "\\r"
    else if c.toNat == 9 then acc ++ "\\t"
    else if c.toNat < 32 then acc ++ " "
    else acc.push c) ""

structure Verdict where
  ok       : Bool
  errs     : Array String
  sorries  : Nat
  ms       : Nat

def Verdict.toJson (v : Verdict) : String :=
  let body := String.intercalate "," (v.errs.toList.map (fun e => "\"" ++ escape e ++ "\""))
  "{\"ok\":" ++ (if v.ok then "true" else "false") ++
  ",\"n_errors\":" ++ toString v.errs.size ++
  ",\"errors\":[" ++ body ++ "]" ++
  ",\"sorries\":" ++ toString v.sorries ++
  ",\"ms\":" ++ toString v.ms ++ "}"

/-- Elaborate one snippet against `baseEnv` in a fresh command state.
    The snippet's own `import` lines are parsed by `parseHeader` and DISCARDED - we continue
    from the post-header parser position against the already-loaded Mathlib. Feeding an
    import line to `processCommands` raises "invalid import command", which is itself one of
    the errors in our failure census. -/
unsafe def checkOne (baseEnv : Environment) (content : String) : IO Verdict := do
  let t0 ← IO.monoMsNow
  let inputCtx := Parser.mkInputContext content "<snippet>"
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  let cmdState := Command.mkState baseEnv messages {}
  let s ← IO.processCommands inputCtx parserState cmdState
  let msgs := s.commandState.messages.toList
  let mut errs : Array String := #[]
  let mut sorries : Nat := 0
  for m in msgs do
    let txt ← m.data.toString
    if m.severity == MessageSeverity.error then
      errs := errs.push s!"{m.pos.line}:{m.pos.column}: {txt}"
    else if (txt.splitOn "sorry").length > 1 then
      -- Match on "sorry" anywhere in a NON-error message, not on the exact phrase
      -- "declaration uses 'sorry'". Measured on Lean v4.31.0-rc1: that exact phrase did not
      -- match and a sorry-ed theorem was counted as sorries=0 - i.e. unproved work would have
      -- been reported as clean. Severity is already known to be non-error at this point.
      sorries := sorries + 1
  let t1 ← IO.monoMsNow
  return { ok := errs.isEmpty, errs := errs, sorries := sorries, ms := t1 - t0 }

/-- Load Mathlib once. Returns (env, milliseconds).

    ⛔ `BATCHD_NO_INIT_EXEC=1` skips `enableInitializersExecution`. This is an EXPERIMENT
    CONTROL, not a config knob. Measured on the compiled binary WITH the call: core-Lean
    notation `+` was absent from the token table ("unexpected token '+'") and `OfNat Nat 1`
    could not be synthesised, while MATHLIB notation (`ℝ`) parsed fine. That asymmetry -
    core broken, Mathlib fine - is the signature of extension-state indices being scrambled
    by re-running initializers that a linked-in binary has ALREADY run at startup. -/
unsafe def loadBase : IO (Environment × Nat) := do
  initSearchPath (← findSysroot)
  let t0 ← IO.monoMsNow
  let skip := (← IO.getEnv "BATCHD_NO_INIT_EXEC") == some "1"
  unless skip do
    Lean.enableInitializersExecution
  -- ⛔ DO NOT hand-roll `importModules` here. Measured: a hand-rolled import produced an
  -- environment that PASSED every direct probe (10,737 modules, `instOfNatNat` present,
  -- "+" present in the token table) and yet elaborated as if nothing were imported -
  -- `ℝ` silently became an auto-bound implicit ("Real.pi has type Real but is expected to
  -- have type ℝ") and `(1:Nat) + 1` died at the `+` with "unexpected token".
  -- `Elab.processHeader` is the path `lean` itself uses; it finalizes the import the way
  -- the elaborator expects (main module set, options threaded, header messages kept).
  let hdrCtx := Parser.mkInputContext ("import Mathlib" ++ (Char.ofNat 10).toString) "<base>"
  let (header, _, hdrMsgs) ← Parser.parseHeader hdrCtx
  let (env, _) ← Elab.processHeader header {} hdrMsgs hdrCtx
  let t1 ← IO.monoMsNow
  return (env, t1 - t0)

/-- Read exactly `n` bytes, or fewer only on EOF. A short read is EOF, never silently zero. -/
partial def readExact (h : IO.FS.Stream) (n : Nat) (acc : ByteArray) : IO ByteArray := do
  if acc.size >= n then return acc
  let chunk ← h.read (USize.ofNat (n - acc.size))
  if chunk.size == 0 then return acc  -- EOF
  readExact h n (acc ++ chunk)

/-- The `--selftest` cases. These are the experiment described in the header: cases 1 and 2
    are exactly the ones that FAILED under the interpreted predecessor. -/
def selftestCases : List (String × String × Bool) :=
  [ ("ofnat-literal",   "def f : Nat := 1", true)
  , ("norm_num-tactic", "theorem t : (1:Nat) + 1 = 2 := by norm_num", true)
  , ("mathlib-symbol",  "example : (2:ℝ) + 2 = 4 := by norm_num", true)
  , ("simp-tactic",     "example (n : Nat) : n + 0 = n := by simp", true)
  , ("real-instances",  "noncomputable def g : ℝ := Real.pi", true)
  , ("bad-code-fails",  "theorem bad : (1:Nat) = 2 := by norm_num", false)
  , ("isolation-a",     "def shared_name : Nat := 1", true)
  , ("isolation-b",     "def shared_name : Nat := 2", true)  -- must NOT clash with isolation-a
  , ("header-stripped", "import Mathlib\ndef h : Nat := 3", true)
  , ("sorry-is-not-error", "theorem s : (1:Nat) = 1 := by sorry", true)
  ]

unsafe def runSelftest : IO UInt32 := do
  let (env, importMs) ← loadBase
  IO.println s!"  [INFO] Mathlib imported in {importMs} ms"
  let mut pass := 0
  let mut total := 0
  for (name, src, expectOk) in selftestCases do
    total := total + 1
    let v ← checkOne env src
    if v.ok == expectOk then
      pass := pass + 1
      IO.println s!"  [PASS] {name} ({v.ms} ms, errors={v.errs.size}, sorries={v.sorries})"
    else
      let detail := if v.errs.isEmpty then "no errors" else v.errs[0]!
      IO.println s!"  [FAIL] {name} expected ok={expectOk} got ok={v.ok}: {detail}"
  -- The sorry case must be ok:true AND sorries:1 - conflating them would hide unproved work.
  total := total + 1
  let vs ← checkOne env "theorem s2 : (1:Nat) = 1 := by sorry"
  if vs.sorries == 1 then
    pass := pass + 1
    IO.println "  [PASS] sorry-counted-separately"
  else
    IO.println s!"  [FAIL] sorry-counted-separately expected sorries=1 got {vs.sorries}"
  IO.println s!"{pass}/{total}"
  return (if pass == total then 0 else 1)

/-- Diagnostic probe. Prints what actually landed in the environment, because the failure
    signature (core `+` missing, Mathlib `ℝ` present) is not explicable from the source alone. -/
unsafe def runDiag : IO UInt32 := do
  let (env, ms) ← loadBase
  IO.println s!"  [INFO] import_ms={ms}"
  IO.println s!"  [INFO] modules={env.header.moduleNames.size} constants_ok={(env.find? `Nat).isSome}"
  for n in [`instOfNatNat, `HAdd.hAdd, `Real.pi, `Nat.add, `Mathlib.Tactic.NormNum.evalAdd] do
    IO.println s!"  [INFO] find {n} = {(env.find? n).isSome}"
  let st := Parser.parserExtension.getState env
  let plus : String := "+"
  IO.println s!"  [INFO] token_table_has_plus={(st.tokens.find? plus).isSome}"
  IO.println s!"  [INFO] cat_term={(st.categories.find? `term).isSome}"
  IO.println s!"  [INFO] mainModule={env.mainModule}"
  -- Probe the parser directly: if this succeeds while a full snippet fails, the fault is in
  -- the command-state plumbing, not in the imported environment.
  match Parser.runParserCategory env `term "1 + 1" with
  | .ok _    => IO.println "  [INFO] runParserCategory term ok"
  | .error e => IO.println s!"  [INFO] runParserCategory term = ERROR {e}"
  let v ← checkOne env "def f : Nat := 1"
  IO.println s!"  [INFO] checkOne(def f : Nat := 1) ok={v.ok} errs={v.errs}"
  return 0

unsafe def serve : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let (env, importMs) ← loadBase
  -- READY on stdout so the client can time startup and know the base env is live.
  stdout.putStrLn s!"\{\"ready\":true,\"import_ms\":{importMs}}"
  stdout.flush
  let mut running := true
  while running do
    let line ← stdin.getLine
    let line := line.trim
    if line == "" then
      running := false          -- EOF: parent went away
    else if line == "QUIT" then
      running := false
    else if line.startsWith "LEN " then
      let n := (line.drop 4).trim.toNat!
      let bytes ← readExact stdin n ByteArray.empty
      if bytes.size < n then
        -- Truncated request. This is BLOCKED, never "0 errors": reporting an unfinished
        -- check as clean is the exact failure mode this whole file exists to prevent.
        stdout.putStrLn s!"\{\"ok\":false,\"n_errors\":1,\"errors\":[\"BLOCKED: truncated request, got {bytes.size} of {n} bytes\"],\"sorries\":0,\"ms\":0}"
        stdout.flush
        running := false
      else
        let src := String.fromUTF8! bytes
        let v ← try checkOne env src
                catch e => pure { ok := false, errs := #[s!"BLOCKED: exception: {toString e}"],
                                  sorries := 0, ms := 0 }
        stdout.putStrLn v.toJson
        stdout.flush
    else
      stdout.putStrLn s!"\{\"ok\":false,\"n_errors\":1,\"errors\":[\"BLOCKED: bad frame: {escape line}\"],\"sorries\":0,\"ms\":0}"
      stdout.flush
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  if args.contains "--diag" then runDiag
  else if args.contains "--selftest" then runSelftest else serve
