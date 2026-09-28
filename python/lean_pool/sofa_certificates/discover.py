"""Recompute adaptive-cover witnesses using the imported rational evaluator."""

import argparse
import json
import subprocess
from pathlib import Path

from lean_pool.sofa_certificates.__main__ import DATA

PREAMBLE = """import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle007
open GerverSofa GerverSofa.PartE

def discoverCover : Nat → AngleCell → String → List (String × Nat × String)
  | depth, cell, path =>
    if physicallyIrrelevant cell then [(path, depth, "irrelevant")]
    else if cellInsideLocal cell then [(path, depth, "local")]
    else if cell.rejected then [(path, depth, "rejected")]
    else match depth with
      | 0 => [(path, 0, "unresolved")]
      | n + 1 =>
        discoverCover n (childLL cell) (path ++ "0") ++
        discoverCover n (childLH cell) (path ++ "1") ++
        discoverCover n (childHL cell) (path ++ "2") ++
        discoverCover n (childHH cell) (path ++ "3")

def childDigit (cell : AngleCell) (digit : Char) : AngleCell :=
  match digit with
  | '0' => childLL cell
  | '1' => childLH cell
  | '2' => childHL cell
  | _ => childHH cell

def rootIndex (i : Nat) : AngleCell :=
  match i with
  | 0 => e24PhiBelowRoot
  | 1 => e24PhiAboveRoot
  | 2 => e24ThetaBelowRoot
  | _ => e24ThetaAboveRoot

"""


def source_text() -> str:
    """Emit the deterministic depth-first search for all 550 cover roots."""
    candidates = json.loads((DATA / "cover-expansion-candidates.json").read_text())
    rows = [
        f'    ({item["id"]}, {item["depth"]}, {item["region"]}, "{item["path"]}")'
        for item in candidates
    ]
    return (
        PREAMBLE
        + """#eval do
  let inputs : List (Nat × Nat × Nat × String) := [
"""
        + ",\n".join(rows)
        + """ ]
  for (id, depth, root, path) in inputs do
    let cell := (String.toList path).foldl childDigit (rootIndex root)
    for (leaf, remaining, reason) in discoverCover depth cell "" do
      IO.println (toString id ++ "|" ++ leaf ++ "|" ++ toString remaining ++
        "|" ++ reason)
  let special := "1101100".toList.foldl childDigit e24PhiAboveRoot
  for (path, depth, reason) in discoverCover 9 special "" do
    IO.println ("COVER|" ++ path ++ "|" ++ toString depth ++ "|" ++ reason)
"""
    )


def discover(pool: Path, workspace: Path) -> None:
    """Run Lean and require byte-identical search output for both witness sets."""
    workspace.mkdir(parents=True, exist_ok=False)
    source = workspace / "Discover.lean"
    source.write_text(source_text())
    result = subprocess.run(
        ["lake", "env", "lean", str(source)],
        cwd=pool,
        capture_output=True,
        text=True,
        check=False,
    )
    (workspace / "stdout.log").write_text(result.stdout)
    (workspace / "stderr.log").write_text(result.stderr)
    result.check_returncode()
    for filename, special in [
        ("cover-bulk-discovery.jsonl", False),
        ("cover-special-discovery.txt", True),
    ]:
        lines = [
            line
            for line in result.stdout.splitlines()
            if (line.startswith("COVER|") if special else line[:1].isdigit())
        ]
        content = "\n".join(lines) + "\n"
        (workspace / filename).write_text(content)
        if content != (DATA / filename).read_text():
            raise ValueError(f"Recomputed witnesses differ: {filename}")
    print("Verified all 10,801 recorded leaves from 550 cover roots")


def main() -> None:
    """Recompute the cover leaves against a built moving-sofa checkout."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pool", type=Path, required=True)
    parser.add_argument("--workspace", type=Path, required=True)
    arguments = parser.parse_args()
    discover(arguments.pool.resolve(), arguments.workspace.resolve())


if __name__ == "__main__":
    main()
