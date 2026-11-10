/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Library with utilities for working with Strata files.
import StrataLaurel.Implementation.Cli

open Strata.Cli (SolverBackend PipelineResolver)

def buildCommandGroups (backends : List SolverBackend := [])
    (resolver : PipelineResolver := {}) : List CommandGroup :=
  Strata.Cli.buildCommandGroups backends resolver [StrataLaurel.Cli.laurelFrontend]

def buildCommandList (backends : List SolverBackend := [])
    (resolver : PipelineResolver := {}) : List Command :=
  Strata.Cli.buildCommandList backends resolver [StrataLaurel.Cli.laurelFrontend]

def buildCommandMap (backends : List SolverBackend := [])
    (resolver : PipelineResolver := {}) : Std.HashMap String Command :=
  Strata.Cli.buildCommandMap backends resolver [StrataLaurel.Cli.laurelFrontend]

#guard (buildCommandList []).length == StrataLaurel.Cli.commandList.length
#guard (buildCommandMap []).size == (buildCommandList []).length
#guard (buildCommandGroups []).map (·.name) == ["Core", "Laurel"]

def commandGroups : List CommandGroup := buildCommandGroups []
def commandList : List Command := buildCommandList []
def commandMap : Std.HashMap String Command := buildCommandMap []
