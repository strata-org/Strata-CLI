# AGENTS.md - StrataCLI

Guide for AI agents working with the StrataCLI package.

## Package Purpose

StrataCLI is the command-line frontend for Strata. It builds the `strata` executable that orchestrates parsing, type-checking, transformation, and analysis (including SMT-based verification) of programs written in Strata dialects (Core, Laurel, Python, C_Simp, B3).

## Architecture

### File Layout

- `StrataMain.lean` - Minimal entry point. Calls `runCommandMap commandMap commandGroups args`. Do not add logic here.
- `StrataMainLib.lean` - Builds the command groups from Strata's Core commands plus the Python and Laurel frontends (`CliFrontend`s). The commands themselves live in other packages:
  - Strata `Strata/Cli/CoreCommands.lean` - `verify`, `transform`, the command builders, `SolverBackend`, `PipelineResolver`.
  - Strata `Strata/Cli/DialectCommands.lean` - `check`, `toIon`, `print`, `diff`.
  - Strata `StrataLaurel/Implementation/Cli.lean` - the Laurel commands and `laurelFrontend`.
  - StrataPythonFrontEnd `StrataPython/Cli.lean` - the Python commands.
  - Strata `Strata/Cli/Framework.lean` - flag parsing, exit codes, help output.

### Exit Codes (namespace `ExitCode`)

| Constant | Value | When to use |
|----------|-------|-------------|
| (success) | 0 | Analysis passed, inconclusive, or `--no-solve` |
| `userError` | 1 | Bad CLI args, malformed source, type errors |
| `failuresFound` | 2 | Verification found assertion violations |
| `internalError` | 3 | SMT encoding bug, solver crash, translation error |
| `knownLimitation` | 4 | Unsupported language construct |

## How to Add a New Command

1. Define a `Command` value in the package that owns it (see File Layout):
   ```lean
   def myNewCommand : Command where
     name := "myNew"
     args := [ "file" ]           -- positional args
     flags := [includeFlag]       -- reuse common flags as needed
     help := "Description of what this command does."
     callback := fun v pflags => do
       let file := v[0]
       -- implementation here
   ```

2. Add it to its group: the Core group in `Strata.Cli.buildCommandGroups`, or the frontend's `CliFrontend`.

3. The command automatically appears in `commandMap` and `--help` output.

### Adding Flags

- Reuse `verifyOptionsFlags` for verification commands.
- Reuse `includeFlag` for commands that load dialect files.
- For new flags, add a `Flag` to the command's `flags` list.
- Access flag values via `pflags.getBool "name"`, `pflags.getString "name"`, or `pflags.getRepeated "name"`.

### Verification Options

Most verification commands build a `VerifyOptions` via `parseVerifyOptions pflags`. This handles all standard flags (solver, timeout, check-mode, etc.). Start from `VerifyOptions.default` or a custom base and the function fills in CLI overrides.

For Laurel commands, use `parseLaurelVerifyOptions` which wraps `parseVerifyOptions` and adds `LaurelTranslateOptions`.

## How to Modify an Existing Command

1. Find the command definition in the file listed under File Layout (search for `def <commandName>Command`).
2. Modify the `callback` implementation, `flags` list, or `args` list.
3. If changing arity (`args`), update the callback's vector indexing accordingly.

## Conventions

- Commands that read Strata files should use `pflags.buildDialectFileMap dialects` to construct the dialect search path (handles `--include` flags and the preloaded dialects).
- Use `readStrataProgram` for reading and parsing program files with error formatting.
- Prefer the structured exit helpers over raw `IO.Process.exit`.
- The `transform` command uses positional flag binding: `--procedures`/`--functions` bind to the most recent `--pass`. This is handled by `buildPassConfigs` which walks `pflags.entries` in order.
- The `pyAnalyzeLaurel` command emits machine-readable `RESULT:` and `DETAIL:` lines on stdout for downstream tooling. Other commands use human-readable output.

## Dependencies

This package imports from:
- `Strata` (parent package) - Core verification logic, languages, transforms, backends
- `StrataDDM` - Dialect Definition Mechanism (parsing, elaboration, Ion format)
- `Lean` - Parser extensions, JSON utilities

Key imports in `StrataMainLib.lean`:
- `StrataLaurel.Implementation.Cli` - the Laurel frontend (`StrataLaurel.Cli.laurelFrontend`), and through it Strata's Core commands and builders
- `StrataPython.Cli` - the Python commands

## Testing

Build and run:
```bash
lake build
lake exe strata --help
lake exe strata verify ${STRATA_PACKAGE_ROOT}/Examples/SimpleProc.core.st
```

## Common Patterns

### Reading a file and running verification
```lean
let fm ← pflags.buildDialectFileMap
let (pgm, inputCtx) ← readStrataProgram fm file
let vcResults ← Strata.Core.verify pgm inputCtx proceduresToVerify opts mkDischarge
```

### Running the Python-to-Laurel pipeline
```lean
let (outcome, stats, pctx) ← Strata.Pipeline.runPyAnalyzePipeline { ... }
```

### Applying transforms
```lean
match ← (Strata.Core.runTransforms initProgram passes).toBaseIO with
| .ok (program, _) => IO.print (Core.formatProgram program)
| .error e => exitFailure s!"Transform failed: {e}"
```

### Translating to GOTO
```lean
match procedureToGotoCtx Env p sourceText (axioms := axioms) (distincts := distincts) with
| .error e => exitInternalError s!"{e}"
| .ok (ctx, liftedFuncs) => ...
```
