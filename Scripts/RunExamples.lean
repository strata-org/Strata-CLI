/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/--
Invokes the run_examples.sh test script.
This file is meant to be run via `#eval` during elaboration,
which will cause `lake build` to fail if the tests fail.
-/
#eval show IO Unit from do
  let result ← IO.Process.output {
    cmd := "bash"
    args := #["scripts/run_examples.sh"]
  }
  IO.print result.stdout
  if result.exitCode != 0 then
    IO.eprint result.stderr
    throw <| IO.userError s!"run_examples.sh failed (exit {result.exitCode})"
