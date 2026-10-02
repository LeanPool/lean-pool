/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

module

import Lean

/-- Generate complete project indexes, or check them without rewriting files. -/
public def main (args : List String) : IO UInt32 := do
  let result ← IO.Process.output {
    cmd := "python3"
    args := #["scripts/project-indexes.py"] ++ args.toArray
  }
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode
