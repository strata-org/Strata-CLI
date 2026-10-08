/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Library with utilities for working with Strata files.
import StrataLaurel.Implementation.Cli
import StrataPython
import StrataPython.Cli
import StrataPython.PyFactory
import StrataPython.Specs.DDM

open Strata.Cli (SolverBackend PipelineResolver)

def pythonFrontend : Strata.Cli.CliFrontend where
  dialects := [StrataPython.Python, StrataPython.Specs.DDM.PythonSpecs]
  group := fun mkDischarge =>
    { name := "Python"
      commands := [StrataPython.Cli.pyAnalyzeLaurelCommand mkDischarge,
                   StrataPython.Cli.pyResolveOverloadsCommand,
                   StrataPython.Cli.pySpecsCommand,
                   StrataPython.Cli.pySpecToLaurelCommand,
                   StrataPython.Cli.pyAnalyzeLaurelToGotoCommand,
                   StrataPython.Cli.pyAnalyzeToGotoCommand,
                   StrataPython.Cli.pyTranslateLaurelCommand,
                   StrataPython.Cli.pyInterpretCommand] }

def buildCommandGroups (backends : List SolverBackend := [])
    (resolver : PipelineResolver := {}) : List CommandGroup :=
  Strata.Cli.buildCommandGroups backends resolver [pythonFrontend, StrataLaurel.Cli.laurelFrontend]

def buildCommandList (backends : List SolverBackend := [])
    (resolver : PipelineResolver := {}) : List Command :=
  Strata.Cli.buildCommandList backends resolver [pythonFrontend, StrataLaurel.Cli.laurelFrontend]

def buildCommandMap (backends : List SolverBackend := [])
    (resolver : PipelineResolver := {}) : Std.HashMap String Command :=
  Strata.Cli.buildCommandMap backends resolver [pythonFrontend, StrataLaurel.Cli.laurelFrontend]

private def expectedPythonGroupSize : Nat := 8

#guard (((buildCommandGroups []).find? (·.name == "Python")).map (·.commands.length)).getD 0 == expectedPythonGroupSize
#guard (buildCommandList []).length == StrataLaurel.Cli.commandList.length + expectedPythonGroupSize
#guard (buildCommandMap []).size == (buildCommandList []).length
#guard (buildCommandGroups []).map (·.name) == ["Core", "Python", "Laurel"]

def commandGroups : List CommandGroup := buildCommandGroups []
def commandList : List Command := buildCommandList []
def commandMap : Std.HashMap String Command := buildCommandMap []
