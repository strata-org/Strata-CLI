/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import Strata.Examples.Embedded

public def main (_args : List String) : IO UInt32 := do
  let tmpDir ← IO.Process.run { cmd := "mktemp", args := #["-d"] }
  let examplesDir := tmpDir.trimAscii.toString

  writeEmbeddedExamples ⟨examplesDir⟩
  IO.println s!"Extracted examples to {examplesDir}"

  let result ← IO.Process.output {
    cmd := "bash"
    args := #["scripts/run_examples.sh", examplesDir]
  }
  IO.print result.stdout
  if result.exitCode != 0 then
    IO.eprint result.stderr
    IO.eprintln s!"run_examples.sh failed (exit {result.exitCode})"
    IO.FS.removeDirAll ⟨examplesDir⟩
    return 1

  IO.FS.removeDirAll ⟨examplesDir⟩
  return 0
