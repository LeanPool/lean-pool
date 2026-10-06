/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.MainResults

/-!
# High-contrast homogenization: Meta.AxiomsAudit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Axiom dependencies of the main results

Building this module prints the axiom dependencies of the theorems of
`HCPoly.MainResults`.  Each must report exactly the three standard foundational
axioms of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

This file is intentionally not imported by the library root, so the report runs
only when it is built explicitly, with `lake build HCPoly.Meta.AxiomsAudit`.
-/
