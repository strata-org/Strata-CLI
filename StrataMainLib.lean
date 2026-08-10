/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Library with utilities for working with Strata files.
import Lean.Parser.Extension
import Strata.Cli.Framework
import Strata.Cli.VerifyOptions
import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.SarifOutput
import Strata.Pipeline.Context
import Strata.Languages.C_Simp.Verify
import Strata.Languages.B3.Verifier.Program
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.C_Simp.DDMTransform.Parse
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel
import Strata.Languages.Core.EntryPoint
import Strata.Transform.ProcedureInlining
import StrataDDM.Util.IO

import Strata.SimpleAPI
import Strata.Util.Json
import StrataDDM.BuiltinDialects
import StrataDDM.Util.String
import StrataPython
import StrataPython.Cli
import StrataPython.PyFactory
import StrataPython.Specs.DDM

open Strata
open StrataPython
open StrataDDM.Elab (LoadedDialects elabProgram)

open Core (VerifyOptions VerboseMode VerificationMode CheckLevel EntryPoint)
open Laurel (LaurelVerifyOptions LaurelTranslateOptions)

/-! ## Dialect file map (unified CLI only)

The unified `strata` binary builds a dialect file map that includes Python
dialects so that subcommands like `check`/`print`/`verify` can handle
Python files. -/

namespace ParsedFlags

def buildDialectFileMap (pflags : ParsedFlags) : IO StrataDDM.DialectFileMap := do
  let preloaded := StrataDDM.Elab.LoadedDialects.builtin
    |>.addDialect! StrataPython.Python
    |>.addDialect! StrataPython.Specs.DDM.PythonSpecs
    |>.addDialect! Strata.Core
    |>.addDialect! C_Simp
    |>.addDialect! B3CST
    |>.addDialect! Strata.Laurel.Laurel
    |>.addDialect! Strata.smtReservedKeywordsDialect
    |>.addDialect! Strata.SMTCore
    |>.addDialect! Strata.SMT
    |>.addDialect! Strata.SMTResponse
  let mut sp ← StrataDDM.DialectFileMap.new preloaded
  for path in pflags.getRepeated "include" do
    match ← sp.add path |>.toBaseIO with
    | .error msg => exitFailure msg
    | .ok sp' => sp := sp'
  return sp

end ParsedFlags

/-- Read and parse a Strata program file via the DDM API. Returns the parsed
    program and the input context (for source location resolution). Throws an
    `IO.userError` with formatted diagnostics on parse failure, and a separate
    error if the file defines a dialect rather than a program. -/
private def readStrataProgram (fm : StrataDDM.DialectFileMap) (file : String)
    : IO (StrataDDM.Program × Lean.Parser.InputContext) := do
  let text ← StrataDDM.Util.readInputSource file
  let displayPath := StrataDDM.Util.displayName file
  let inputCtx := Lean.Parser.mkInputContext text displayPath
  match ← StrataDDM.readStrataText fm displayPath text.toUTF8 with
  | .program pgm => pure (pgm, inputCtx)
  | .dialect _ =>
    throw (IO.userError s!"Expected a program file, got a dialect: {file}")

def checkCommand : Command where
  name := "check"
  args := [ "file" ]
  flags := [includeFlag]
  help := "Parse and validate a Strata file (text or Ion). Reports errors and exits."
  callback := fun v pflags => do
    let fm ← pflags.buildDialectFileMap
    let _ ← StrataDDM.readStrataFile fm v[0]

def toIonCommand : Command where
  name := "toIon"
  args := [ "input", "output" ]
  flags := [includeFlag]
  help := "Convert a Strata text file to Ion binary format."
  callback := fun v pflags => do
    let searchPath ← pflags.buildDialectFileMap
    let pd ← StrataDDM.readStrataFile searchPath v[0]
    match pd with
    | .dialect d =>
      IO.FS.writeBinFile v[1] d.toIon
    | .program pgm =>
      IO.FS.writeBinFile v[1] pgm.toIon

def printCommand : Command where
  name := "print"
  args := [ "file" ]
  flags := [includeFlag]
  help := "Pretty-print a Strata file (text or Ion) to stdout."
  callback := fun v pflags => do
    let searchPath ← pflags.buildDialectFileMap
    -- Special case for already loaded dialects.
    let ld ← searchPath.getLoaded
    if mem : v[0] ∈ ld.dialects then
      IO.print <| ld.dialects.format v[0] mem
      return
    let pd ← StrataDDM.readStrataFile searchPath v[0]
    match pd with
    | .dialect d =>
      let ld ← searchPath.getLoaded
      let .isTrue mem := (inferInstance : Decidable (d.name ∈ ld.dialects))
        | exitInternalError "Internal error reading file."
      IO.print <| ld.dialects.format d.name mem
    | .program pgm =>
      IO.print <| toString pgm

def diffCommand : Command where
  name := "diff"
  args := [ "file1", "file2" ]
  flags := [includeFlag]
  help := "Compare two program files for syntactic equality. Reports the first difference found."
  callback := fun v pflags => do
    let fm ← pflags.buildDialectFileMap
    let p1 ← StrataDDM.readStrataFile fm v[0]
    let p2 ← StrataDDM.readStrataFile fm v[1]
    match p1, p2 with
    | .program p1, .program p2 =>
      if p1.dialect != p2.dialect then
        exitFailure s!"Dialects differ: {p1.dialect} and {p2.dialect}"
        let Decidable.isTrue eq := (inferInstance : Decidable (p1.commands.size = p2.commands.size))
          | exitFailure s!"Number of commands differ {p1.commands.size} and {p2.commands.size}"
        for (c1, c2) in Array.zip p1.commands p2.commands do
          if c1 != c2 then
            exitFailure s!"Commands differ: {repr c1} and {repr c2}"
    | _, _ =>
      exitFailure "Cannot compare dialect def with another dialect/program."


def laurelAnalyzeBinaryCommand : Command where
  name := "laurelAnalyzeBinary"
  args := []
  flags := verifyOptionsFlags
  help := "Verify Laurel Ion programs read from stdin and print diagnostics. Combines multiple input files."
  callback := fun _ pflags => do
    let options ← parseLaurelVerifyOptions pflags
    let stdinBytes ← (← IO.getStdin).readBinToEnd
    let combinedProgram ← Strata.readLaurelIonProgram stdinBytes
    let diagnostics ← Strata.Laurel.verifyToMessages combinedProgram options

    IO.println s!"==== DIAGNOSTICS ===="
    for diag in diagnostics do
      IO.println s!"{Std.format diag.fileRange.file}:{diag.fileRange.range.start}-{diag.fileRange.range.stop}: {diag.message}"

/-- Normalize a procedure name for `--entry` matching. JVerify lowers a static
    method `pkg.Class.method` to a Core procedure named `pkg.Class?static_method`,
    so we drop the `?static` marker and treat the user-facing `#` separator as `_`.
    This lets `--entry pkg.Class#method` resolve regardless of those details. -/
private def normalizeEntryName (s : String) : String :=
  (s.replace "?static" "").replace "#" "_"

/-- Resolve a `--entry` procedure by name: try an exact match first, then fall
    back to matching on the normalized name. Used only when `--entry` is given
    as an explicit override of the producer's entry-point metadata. -/
private def resolveEntryByName (prog : Core.Program) (entry : String) : Option Core.Procedure :=
  match Core.Program.Procedure.find? prog ⟨entry, ()⟩ with
  | some p => some p
  | none =>
    let target := normalizeEntryName entry
    prog.decls.findSome? fun d =>
      match d.getProc? with
      | some p => if normalizeEntryName p.header.name.name == target then some p else none
      | none => none

/-- Flags for the Laurel interpret commands: `--fuel`, `--entry`, and
    `--keep-all-files`. Shared by `laurelInterpret` (file input) and
    `laurelInterpretBinary` (stdin input). Deliberately excludes the
    solver-oriented flags in `verifyOptionsFlags` — the interpreter never
    invokes a solver, so those would be silently ignored. -/
private def laurelInterpretFlags : List Flag :=
  [{ name := "fuel", help := "Maximum execution steps.", takesArg := .arg "n" },
   { name := "entry",
     help := "Override the entry point to execute, by procedure name. \
              Defaults to the procedure(s) the producer marked with `entry` \
              in the Laurel source.",
     takesArg := .arg "proc" },
   { name := "keep-all-files",
     help := "Store intermediate programs in <dir>.",
     takesArg := .arg "dir" }]

/-- Concretely execute a Laurel Ion program (already loaded as bytes) and print
    diagnostics. Shared implementation of `laurelInterpret` (file input) and
    `laurelInterpretBinary` (stdin input). `inputFile` is the source path, if
    any — used only to derive the `--keep-all-files` base name (stdin has none,
    which `keepAllFilesBaseName` maps to `program`). -/
private def runLaurelInterpret (ionBytes : ByteArray) (pflags : ParsedFlags)
    (inputFile : Option String := none) : IO Unit := do
  let options ← parseLaurelVerifyOptions pflags (inputFile := inputFile)
  -- Reject `0` explicitly: `runEntry` would return `OutOfFuel` before executing
  -- anything, which surfaces as exit 2 (failures found) with an empty diagnostics
  -- block — indistinguishable from a run that really did exhaust its budget, or
  -- worse, misread as assertion failures. Negatives are already rejected by
  -- `toNat?`.
  let fuel ← match pflags.getString "fuel" with
    | some s => match s.toNat? with
      | .some 0 => exitFailure s!"Invalid fuel: '0' (must be > 0)"
      | .some n => pure n
      | .none => exitFailure s!"Invalid fuel: '{s}'"
    | none => pure 10000
  let entryOverride := pflags.getString "entry"

  let combinedProgram ← Strata.readLaurelIonProgram ionBytes

  -- Laurel → Core, mirroring the verify path's translate step.
  let core ← match ← Strata.Laurel.translate { options.translateOptions with analysisMode := .Execute } combinedProgram with
    | (some core, _diags) => pure core
    | (none, diags) => exitFailure s!"Laurel to Core translation failed: {diags.map (·.message)}"

  -- Type-check with the default Core factory (the Laurel verify path uses
  -- `Lambda.Factory.default`, not the Python `ReFactory`).
  let core ← match Core.typeCheck Core.VerifyOptions.quiet core with
    | .ok prog => pure prog
    | .error e => exitFailure s!"Core type checking failed: {e.message}"

  -- Make bodied functions unfold during concrete execution.
  let core := Core.Program.inlineBodiedFunctions core

  -- Persist the exact program the interpreter executes — the form produced
  -- after the interpret-specific type-check + `inlineBodiedFunctions` steps.
  -- Translation's per-pass intermediates stop before these steps, so under
  -- `--keep-all-files` this is the most useful artifact for debugging an
  -- interpret run. Mirrors the pipeline's `{prefix}.<...>.core.st` naming;
  -- the prefix directory is already created by the translate pipeline above.
  if let some pfx := options.translateOptions.keepAllFilesPrefix then
    IO.FS.writeFile s!"{pfx}.interpret.core.st" (toString (Std.format core))

  -- Determine which procedures to execute. An explicit --entry overrides the
  -- producer's markers; otherwise run every procedure marked `entry`.
  let entries ← match entryOverride with
    | some name => match resolveEntryByName core name with
      | some p => pure [p]
      | none => exitFailure s!"entry procedure '{name}' not found"
    | none =>
      match Core.Program.entryProcedures core with
      | [] => exitFailure "no entry point found: mark a procedure with `entry` in the \
                           Laurel source, or pass --entry <proc>"
      | ps => pure ps

  -- Run the entries. `interpretEntries` is shared with the Laurel execute
  -- tests, so the evaluator configuration this command depends on — `assume`s
  -- treated as no-ops, and every assertion failure collected rather than
  -- halting on the first — is defined and regression-tested in one place.
  let outcome ← match Core.Program.interpretEntries core entries fuel with
    | .ok outcome => pure outcome
    | .error diag => exitFailure s!"interpreter setup failed: {diag}"

  IO.println s!"==== DIAGNOSTICS ===="
  -- Assertion failures go to stdout, mapped back to source where possible, so
  -- a single diagnostic-parsing contract catches every assertion violation.
  for diag in outcome.diagnostics do
    IO.println s!"{Std.format diag.fileRange.file}:{diag.fileRange.range.start}-{diag.fileRange.range.stop}: {diag.message}"
  for (procName, label) in outcome.unmapped do
    IO.println s!"<no source>: assertion '{label}' in '{procName}' does not hold"
  -- OutOfFuel, Misc, etc. — these have no source range; surface raw.
  for (procName, e) in outcome.errors do
    IO.eprintln s!"'{procName}': {Imperative.EvalError.toFormat (P := Core.Expression) e}"
  -- Assertion failures are reported as diagnostics above; the caller infers
  -- failure by parsing the `==== DIAGNOSTICS ====` output. Opaque failures
  -- (out of fuel / internal errors) carry no diagnostic, so signal those
  -- through the exit code directly.
  unless outcome.errors.isEmpty do
    IO.Process.exit ExitCode.failuresFound

def laurelInterpretCommand : Command where
  name := "laurelInterpret"
  args := [ "file" ]
  flags := laurelInterpretFlags
  help := "Concretely interpret a Laurel Ion program read from the given file (Laurel → Core → execute) \
           and print diagnostics. The entry point is the procedure marked `entry` by the \
           producer (or, if given, --entry by name); it is run with contracts treated as \
           runtime assertions and `assume`s treated as no-ops. \
           Assertion violations are reported as diagnostics under `==== DIAGNOSTICS ====` on \
           stdout (the caller detects failures by parsing them); the process still exits 0. A \
           non-zero exit code is reserved for errors that carry no diagnostic (out of fuel, \
           internal errors, setup failures)."
  callback := fun v pflags => do
    let ionBytes ← IO.FS.readBinFile v[0]
    runLaurelInterpret ionBytes pflags (inputFile := some v[0])

def laurelInterpretBinaryCommand : Command where
  name := "laurelInterpretBinary"
  args := []
  flags := laurelInterpretFlags
  help := "Concretely interpret a Laurel Ion program read from stdin (Laurel → Core → execute) \
           and print diagnostics. Combines multiple input files. See `laurelInterpret` for \
           the entry-point selection rules and the diagnostic/exit-code contract."
  callback := fun _ pflags => do
    let ionBytes ← (← IO.getStdin).readBinToEnd
    runLaurelInterpret ionBytes pflags

def laurelParseCommand : Command where
  name := "laurelParse"
  args := [ "file" ]
  help := "Parse a Laurel source file (no verification)."
  callback := fun v _ => do
    let _ ← Strata.readLaurelTextFile v[0]
    IO.println "Parse successful"

def laurelAnalyzeCommand : Command where
  name := "laurelAnalyze"
  args := [ "file" ]
  flags := verifyOptionsFlags
  help := "Analyze a Laurel source file. Write diagnostics to stdout."
  callback := fun v pflags => do
    let options ← parseLaurelVerifyOptions pflags (inputFile := some v[0])
    let laurelProgram ← Strata.readLaurelTextFile v[0]
    let (vcResultsOption, errors) ← Strata.Laurel.verifyToVcResults laurelProgram options
    if !errors.isEmpty then
      IO.println s!"==== ERRORS ===="
    for err in errors do
      IO.println s!"{err.message}"
    match vcResultsOption with
    | none => return
    | some vcResults =>
      IO.println s!"==== RESULTS ===="
      for vc in vcResults do
        IO.println s!"{vc.obligation.label}: {match vc.outcome with | .ok o => repr o | .error e => toString e}"

def laurelAnalyzeToGotoCommand : Command where
  name := "laurelAnalyzeToGoto"
  args := [ "file" ]
  help := "Translate a Laurel source file to CProver GOTO JSON files."
  callback := fun v _ => do
    let path : System.FilePath := v[0]
    let content ← IO.FS.readFile path
    let laurelProgram ← Strata.parseLaurelText path content
    match ← Strata.Laurel.translate {} laurelProgram with
      | (none, diags) => exitFailure s!"Core translation errors: {diags.map (·.message)}"
      | (some coreProgram, errors) =>
        let Ctx := { Lambda.LContext.default with functions := Core.Factory, knownTypes := Core.KnownTypes }
        let Env := Lambda.TEnv.default
        let (tcPgm, _) ← match Core.Program.typeCheck Ctx Env coreProgram with
          | .ok r => pure r
          | .error e => exitInternalError s!"{e.format none}"
        let procs := tcPgm.decls.filterMap fun d => d.getProc?
        let funcs := tcPgm.decls.filterMap fun d =>
          match d.getFunc? with
          | some f =>
            let name := Core.CoreIdent.toPretty f.name
            if f.body.isSome && f.typeArgs.isEmpty
              && name != "Int.DivT" && name != "Int.ModT"
            then some f else none
          | none => none
        if procs.isEmpty && funcs.isEmpty then exitInternalError "No procedures or functions found"
        let baseName := StrataPython.Cli.deriveBaseName path.toString
        let typeSyms ← match collectExtraSymbols tcPgm with
          | .ok s => pure s
          | .error e => exitInternalError s!"{e}"
        let typeSymsJson := Lean.toJson typeSyms
        let sourceText := some content
        let axioms := tcPgm.decls.filterMap fun d => d.getAxiom?
        let distincts := tcPgm.decls.filterMap fun d => match d with
          | .distinct name es _ => some (name, es) | _ => none
        let mut symtabPairs : List (String × Lean.Json) := []
        let mut gotoFns : Array Lean.Json := #[]
        let mut allLiftedFuncs : List Core.Function := []
        for p in procs do
          let procName := Core.CoreIdent.toPretty p.header.name
          match procedureToGotoCtx Env p (sourceText := sourceText) (axioms := axioms) (distincts := distincts)
                with
          | .error e => exitInternalError s!"{e}"
          | .ok (ctx, liftedFuncs) =>
            allLiftedFuncs := allLiftedFuncs ++ liftedFuncs
            let json ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson procName ctx)
            match json.symtab with
            | .obj m => symtabPairs := symtabPairs ++ m.toList
            | _ => pure ()
            match json.goto with
            | .obj m =>
              match m.toList.find? (·.1 == "functions") with
              | some (_, .arr fns) => gotoFns := gotoFns ++ fns
              | _ => pure ()
            | _ => pure ()
        for f in funcs ++ allLiftedFuncs do
          let funcName := Core.CoreIdent.toPretty f.name
          match functionToGotoCtx Env f with
          | .error e => exitInternalError s!"{e}"
          | .ok ctx =>
            let json ← IO.ofExcept (CoreToGOTO.CProverGOTO.Context.toJson funcName ctx)
            match json.symtab with
            | .obj m => symtabPairs := symtabPairs ++ m.toList
            | _ => pure ()
            match json.goto with
            | .obj m =>
              match m.toList.find? (·.1 == "functions") with
              | some (_, .arr fns) => gotoFns := gotoFns ++ fns
              | _ => pure ()
            | _ => pure ()
        match typeSymsJson with
        | .obj m => symtabPairs := symtabPairs ++ m.toList
        | _ => pure ()
        -- Deduplicate: keep first occurrence of each symbol name (proper function
        -- symbols come before basic symbol references from callers)
        let mut seen : Std.HashSet String := {}
        let mut dedupPairs : List (String × Lean.Json) := []
        for (k, v) in symtabPairs do
          if !seen.contains k then
            seen := seen.insert k
            dedupPairs := dedupPairs ++ [(k, v)]
        -- Add CBMC default symbols (architecture constants, builtins)
        -- and wrap in {"symbolTable": ...} for symtab2gb
        let symtabObj := dedupPairs.foldl
          (fun (acc : Std.TreeMap.Raw String Lean.Json) (k, v) => acc.insert k v)
          .empty
        let symtab := CProverGOTO.wrapSymtab symtabObj (moduleName := baseName)
        let goto := Lean.Json.mkObj [("functions", Lean.Json.arr gotoFns)]
        let symTabFile := s!"{baseName}.symtab.json"
        let gotoFile := s!"{baseName}.goto.json"
        writeJsonFile symTabFile symtab
        writeJsonFile gotoFile goto
        IO.println s!"Written {symTabFile} and {gotoFile}"

def laurelPrintCommand : Command where
  name := "laurelPrint"
  args := []
  help := "Read Laurel Ion from stdin and print in concrete syntax to stdout."
  callback := fun _ _ => do
    let stdinBytes ← (← IO.getStdin).readBinToEnd
    let program ← Strata.readLaurelIonProgram stdinBytes
    let p := Strata.laurelToStrataProgram program
    let c := p.formatContext {}
    let s := p.formatState
    let fmt := p.commands.foldl (init := f!"") fun f cmd =>
      f ++ (StrataDDM.mformat cmd c s).format
    IO.println (fmt.pretty 100)

def prettyPrintCore (p : Core.Program) : String :=
  let decls := p.decls.map fun d =>
    let s := toString (Std.format d)
    -- Add newlines after major sections in procedures
    s.replace "preconditions:" "\n  preconditions:"
     |>.replace "postconditions:" "\n  postconditions:"
     |>.replace "body:" "\n  body:\n    "
     |>.replace "assert [" "\n    assert ["
     |>.replace "init (" "\n    init ("
     |>.replace "while (" "\n    while ("
     |>.replace "if (" "\n      if ("
     |>.replace "call [" "\n    call ["
     |>.replace "else{" "\n      else {"
     |>.replace "}}" "}\n    }"
  String.intercalate "\n" decls

def laurelToCoreCommand : Command where
  name := "laurelToCore"
  args := [ "file" ]
  help := "Translate a Laurel source file to Core and print to stdout."
  callback := fun v _ => do
    let laurelProgram ← Strata.readLaurelTextFile v[0]
    let (coreProgramOption, errors) ← Strata.Laurel.translate {} laurelProgram
      if !errors.isEmpty then
        IO.println s!"Core translation errors: {errors.map (·.message)}"
      match coreProgramOption with
      | none => return
      | some coreProgram => IO.println (prettyPrintCore coreProgram)

/-! Canonical phase names (`AbstractedPhase.name`) for the passes supported
    by the `transform` command. The CLI's help text and pass dispatch use
    these instead of string literals, so they cannot drift from the
    registry in `Strata.Languages.Core`. -/

private def inlineProceduresPass : String := Strata.Core.passInlineAll.phase.name
private def insertLoopInvariantAssertsPass : String := Strata.Core.passInsertLoopInvariantAsserts.phase.name
private def loopElimPass : String := Strata.Core.passLoopElim.phase.name
private def callElimPass : String := Strata.Core.passCallElim.phase.name
private def filterProceduresPass : String := (Strata.Core.passFilterProcedures []).phase.name
private def removeIrrelevantAxiomsPass : String := (Strata.Core.passRemoveIrrelevantAxioms []).phase.name

private def validPasses : String := String.intercalate ", " [
  inlineProceduresPass, insertLoopInvariantAssertsPass, loopElimPass,
  callElimPass, filterProceduresPass, removeIrrelevantAxiomsPass]

/-- A single transform pass together with the `--procedures`/`--functions`
    that were specified immediately after it on the command line. -/
private structure PassConfig where
  name : String
  procedures : List String := []
  functions : List String := []
deriving Inhabited

/-- Walk the ordered flag entries and bind each `--procedures`/`--functions`
    to the most recent `--pass`. -/
private def buildPassConfigs (entries : Array (String × Option String))
    : IO (Array PassConfig) := do
  let mut configs : Array PassConfig := #[]
  for (flag, value) in entries do
    match flag with
    | "pass" => configs := configs.push { name := value.getD "" }
    | "procedures" =>
      let some cur := configs.back? | exitFailure "--procedures must appear after a --pass"
      let procs := (value.getD "").splitToList (· == ',')
      configs := configs.pop.push { cur with procedures := cur.procedures ++ procs }
    | "functions" =>
      let some cur := configs.back? | exitFailure "--functions must appear after a --pass"
      let fns := (value.getD "").splitToList (· == ',')
      configs := configs.pop.push { cur with functions := cur.functions ++ fns }
    | _ => pure ()
  return configs

def transformCommand : Command where
  name := "transform"
  args := [ "file" ]
  flags := [
    includeFlag,
    { name := "pass",
      help := s!"Transform pass to apply (repeatable, applied left to right). \
               Valid passes: {validPasses}. \
               --procedures and --functions after a --pass apply to that pass.",
      takesArg := .repeat "name" },
    { name := "procedures",
      help := s!"Comma-separated procedure names for the preceding --pass. \
               For {filterProceduresPass}: procedures to keep. \
               For {inlineProceduresPass}: procedures to inline.",
      takesArg := .repeat "procs" },
    { name := "functions",
      help := s!"Comma-separated function names for the preceding --pass (used by {removeIrrelevantAxiomsPass}).",
      takesArg := .repeat "funcs" }]
  help := "Apply one or more transforms to a Core program and print the result."
  callback := fun v pflags => do
    let file := v[0]
    let passConfigs ← buildPassConfigs pflags.entries
    if passConfigs.isEmpty then
      exitFailure s!"No --pass specified. Valid passes: {validPasses}."
    let fm ← pflags.buildDialectFileMap
    -- Read and parse the Core program
    let (pgm, _) ← readStrataProgram fm file
    match Strata.strataProgramToCore pgm with
    | .error msg =>
      exitFailure msg
    | .ok initProgram =>
      -- Validate and convert pass configs to TransformPass values.
      let mut passes : List Core.PipelinePhase := []
      for pc in passConfigs do
        if pc.name == inlineProceduresPass then
          if pc.procedures.isEmpty then
            passes := passes ++ [Strata.Core.passInlineAll]
          else
            passes := passes ++ [Strata.Core.passInlineMatching pc.procedures]
        else if pc.name == insertLoopInvariantAssertsPass then
          passes := passes ++ [Strata.Core.passInsertLoopInvariantAsserts]
        else if pc.name == loopElimPass then
          passes := passes ++ [Strata.Core.passLoopElim]
        else if pc.name == callElimPass then
          passes := passes ++ [Strata.Core.passCallElim]
        else if pc.name == filterProceduresPass then
          if pc.procedures.isEmpty then
            exitFailure s!"{filterProceduresPass} requires --procedures"
          passes := passes ++ [Strata.Core.passFilterProcedures pc.procedures]
        else if pc.name == removeIrrelevantAxiomsPass then
          if pc.functions.isEmpty then
            exitFailure s!"{removeIrrelevantAxiomsPass} requires --functions"
          passes := passes ++ [Strata.Core.passRemoveIrrelevantAxioms pc.functions]
        else
          exitFailure s!"Unknown pass '{pc.name}'. Valid passes: {validPasses}."
      -- Run all passes in a single CoreTransformM chain so fresh variable
      -- counters accumulate and cached analyses are reused across passes.
      match ← (Strata.Core.runTransforms initProgram passes).toBaseIO with
      | .ok (program, _) => IO.print (Core.formatProgram program)
      | .error e => exitFailure s!"Transform failed: {e}"

def verifyCommand (mkDischarge : Core.MkDischargeFn := Core.mkDischargeFn) : Command where
  name := "verify"
  args := [ "file" ]
  flags := includeFlag :: verifyOptionsFlags ++ [
    { name := "check", help := "Process up until SMT generation, but don't solve." },
    { name := "type-check", help := "Exit after semantic dialect's type inference/checking." },
    { name := "parse-only", help := "Exit after DDM parsing and type checking." },
    { name := "output-format", help := "Output format (only 'sarif' supported).", takesArg := .arg "format" },
    { name := "procedures", help := "Verify only the specified procedures (comma-separated).", takesArg := .arg "procs" }]
  help := "Verify a Strata program file (.core.st, .csimp.st, or .b3.st)."
  callback := fun v pflags => do
    let file := v[0]
    let proceduresToVerify := pflags.getString "procedures" |>.map (·.splitToList (· == ','))
    let opts ← parseVerifyOptions pflags { VerifyOptions.default with verbose := .quiet }
      (inputFile := some file)
    let opts := { opts with
      checkOnly := pflags.getBool "check",
      typeCheckOnly := pflags.getBool "type-check",
      parseOnly := pflags.getBool "parse-only",
      outputSarif := opts.outputSarif || pflags.getString "output-format" == some "sarif" }
    -- `--keep-all-files` has no effect for B3 files: the B3 pipeline runs no
    -- Core transform phases, so there are no intermediate programs to emit.
    -- Reject it up front — before the parse-only / type-check-only early
    -- returns below, which would otherwise silently ignore the flag — and exit
    -- with the user-error code (1), not internal-error (3).
    if (file.endsWith ".b3.st" || file.endsWith ".b3cst.st") && opts.keepAllFilesPrefix.isSome then
      exitUserError "--keep-all-files is not supported for B3 files (.b3.st/.b3cst.st)."
    let fm ← pflags.buildDialectFileMap
    let mode := if opts.profile then Strata.Pipeline.OutputMode.profile else .quiet
    let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := mode)
    let (pgm, inputCtx) ← pctx.withPhase "parse" do readStrataProgram fm file
    println! s!"Successfully parsed."
      if opts.parseOnly then return
      if opts.typeCheckOnly then
        let ans := if file.endsWith ".csimp.st" then
                     C_Simp.typeCheck pgm opts
                   else
                     typeCheck inputCtx pgm opts
        match ans with
        | .error e =>
          println! f!"{e.formatRange (some inputCtx.fileMap) true} {e.message}"
          IO.Process.exit ExitCode.userError
        | .ok _ =>
          println! f!"Program typechecked."
          return
      -- Full verification
      let vcResults ← try
        if file.endsWith ".csimp.st" then
          C_Simp.verify pgm opts (mkDischarge := mkDischarge)
        else if file.endsWith ".b3.st" || file.endsWith ".b3cst.st" then
          let ast ← match B3.Verifier.programToB3AST pgm with
            | Except.error msg => throw (IO.userError s!"Failed to convert to B3 AST: {msg}")
            | Except.ok ast => pure ast
          let solver ← B3.Verifier.createInteractiveSolver opts.solver
          let reports ← B3.Verifier.programToSMT ast solver
          for report in reports do
            IO.println s!"\nProcedure: {report.procedureName}"
            for (result, _) in report.results do
              let marker := if result.result.isError then "✗" else "✓"
              let desc := match result.result with
                | .error .counterexample => "counterexample found"
                | .error .unknown => "unknown"
                | .error .refuted => "refuted"
                | .success .verified => "verified"
                | .success .reachable => "reachable"
                | .success .reachabilityUnknown => "reachability unknown"
              IO.println s!"  {marker} {desc}"
          pure #[]
        else if pgm.dialect == "Boole" then
          -- TODO: this will be restored once StrataMainLib is in a separate
          -- package that can depend on the StrataBoole package.
          throw <| IO.Error.userError "Boole dialect support requires the StrataBoole package"
        else
          Strata.Core.verify pgm inputCtx proceduresToVerify opts
            (mkDischarge := mkDischarge) (pipelineCtx := pctx)
      catch e =>
        println! f!"{e}"
        IO.Process.exit ExitCode.internalError
      if opts.outputSarif then
        if file.endsWith ".csimp.st" then
          println! "SARIF output is not supported for C_Simp files (.csimp.st) because location metadata is not preserved during translation to Core."
        else
          let uri := Strata.Uri.file file
          let files := Map.empty.insert uri inputCtx.fileMap
          Core.Sarif.writeSarifOutput opts.checkMode files vcResults (file ++ ".sarif")
      for vcResult in vcResults do
        let posStr := Imperative.MetaData.formatFileRangeD vcResult.obligation.metadata (some inputCtx.fileMap)
        -- `formatOutcome` omits the counterexample model, so render it here,
        -- inline on the obligation line to keep one line per obligation for
        -- tools that parse this output.
        let modelFmt :=
          if vcResult.verbose >= .models && !vcResult.lexprModel.isEmpty then
            f!" Model: {Std.format vcResult.lexprModel}"
          else f!""
        println! f!"{posStr} [{vcResult.obligation.label}]: \
                      {vcResult.formatOutcome}{modelFmt}"
      let success := vcResults.all Core.VCResult.isSuccess
      if success && !opts.checkOnly then
        println! f!"All {vcResults.size} goals passed."
      else if success && opts.checkOnly then
        println! f!"Skipping verification."
      else
        let provedGoalCount := (vcResults.filter Core.VCResult.isSuccess).size
        let failedGoalCount := (vcResults.filter Core.VCResult.isNotSuccess).size
        -- Encoding failures, solver crashes, or per-check SMT errors (exit 3)
        let hasImplError := vcResults.any (fun r => r.isImplementationError || r.hasSMTError)
        -- Assertion violations that are not timeouts or internal errors (exit 2)
        let hasFailure := vcResults.any (fun r => !r.isSuccess && !r.isTimeout && !r.isImplementationError && !r.hasSMTError)
        println! f!"Finished with {provedGoalCount} goals passed, {failedGoalCount} failed."
        if hasImplError then
          IO.Process.exit ExitCode.internalError
        else if hasFailure then
          IO.Process.exit ExitCode.failuresFound

/-- A named solver backend: the `--solver` value it answers to and the discharge
    factory that handles verification queries for that solver. -/
structure SolverBackend where
  name : String
  mkDischarge : Core.MkDischargeFn

/-- Build one discharge factory that picks a backend by the `--solver` value,
    falling back to the default process solver when none matches. -/
private def dispatchDischarge (backends : List SolverBackend) : Core.MkDischargeFn :=
  fun options counter tempDir vars md label termCache ctx =>
    match backends.find? (·.name == options.solver) with
    | some b => b.mkDischarge options counter tempDir vars md label termCache ctx
    | none   => Core.mkDischargeFn options counter tempDir vars md label termCache ctx

/-- Build the command groups, wiring the solver-aware commands to dispatch over
    the given backends. -/
def buildCommandGroups (backends : List SolverBackend := []) : List CommandGroup :=
  let mkDischarge := dispatchDischarge backends
  [ { name := "Core"
      commands := [verifyCommand mkDischarge, transformCommand, checkCommand, toIonCommand, printCommand, diffCommand]
      commonFlags := [includeFlag] },
    { name := "Python"
      commands := [StrataPython.Cli.pyAnalyzeLaurelCommand mkDischarge,
                   StrataPython.Cli.pyResolveOverloadsCommand,
                   StrataPython.Cli.pySpecsCommand,
                   StrataPython.Cli.pySpecToLaurelCommand,
                   StrataPython.Cli.pyAnalyzeLaurelToGotoCommand,
                   StrataPython.Cli.pyAnalyzeToGotoCommand,
                   StrataPython.Cli.pyTranslateLaurelCommand,
                   StrataPython.Cli.pyInterpretCommand] },
    { name := "Laurel"
      commands := [laurelAnalyzeCommand, laurelAnalyzeBinaryCommand,
                   laurelInterpretCommand, laurelInterpretBinaryCommand,
                   laurelAnalyzeToGotoCommand, laurelParseCommand,
                   laurelPrintCommand, laurelToCoreCommand] },
  ]

def buildCommandList (backends : List SolverBackend := []) : List Command :=
  (buildCommandGroups backends).foldl (init := []) fun acc g => acc ++ g.commands

def buildCommandMap (backends : List SolverBackend := []) : Std.HashMap String Command :=
  (buildCommandList backends).foldl (init := {}) fun m c => m.insert c.name c

-- The command names StrataCLI itself owns (the Core and Laurel groups), sorted.
-- The Python group's commands live in the external `StrataPython.Cli` package, so
-- its names are counted rather than pinned here — pinning them couples this build
-- to routine frontend renames.
private def expectedOwnedCommandNames : List String :=
  ["check", "diff",
   "laurelAnalyze", "laurelAnalyzeBinary", "laurelAnalyzeToGoto",
   "laurelInterpret", "laurelInterpretBinary", "laurelParse",
   "laurelPrint", "laurelToCore", "print",
   "toIon", "transform", "verify"]

private def expectedPythonGroupSize : Nat := 8

-- Names of the commands StrataCLI owns (everything outside the Python group).
private def ownedCommandNames (backends : List SolverBackend := []) : List String :=
  ((buildCommandGroups backends).filter (·.name != "Python")).foldl
    (init := []) (fun acc g => acc ++ g.commands.map (·.name))
    |>.mergeSort (· < ·)

-- A throwaway backend (reuses the default discharge factory) so the guards below
-- can exercise a non-empty registry without needing an external solver to build.
private def incrementalBackend : SolverBackend where
  name := "incremental"
  mkDischarge := fun options counter tempDir vars md label termCache ctx =>
    Core.mkDischargeFn { options with incremental := true }
      counter tempDir vars md label termCache ctx

-- StrataCLI's owned commands are exactly this set; the external Python group
-- contributes a fixed count; the map and list agree on size (no duplicate names).
#guard ownedCommandNames [] == expectedOwnedCommandNames
#guard (((buildCommandGroups []).find? (·.name == "Python")).map (·.commands.length)).getD 0 == expectedPythonGroupSize
#guard (buildCommandList []).length == expectedOwnedCommandNames.length + expectedPythonGroupSize
#guard (buildCommandMap []).size == (buildCommandList []).length

-- Adding a backend does not change the exposed command set.
#guard (buildCommandMap [incrementalBackend]).size == (buildCommandMap []).size
#guard ownedCommandNames [incrementalBackend] == expectedOwnedCommandNames

def commandGroups : List CommandGroup := buildCommandGroups []
def commandList : List Command := buildCommandList []
def commandMap : Std.HashMap String Command := buildCommandMap []
