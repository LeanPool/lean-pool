/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import LeanPool.MovingSofa.Optimality
public import LeanPool.MovingSofa.Motion.Applications.Development002
public import LeanPool.MovingSofa.External
/-!
# The moving sofa problem: proofs

Proves the three statements of `MovingSofaSubmission.Challenge`. Two of them are proved in
earlier files and are available here by import: `MovingSofa.GerversSofa.ABφθSpec.existsUnique`
in `MovingSofa.Canonical.Definitions`, and `MovingSofa.isMovingSofa_gerversSofa` in
`MovingSofa.Gerver.Motion`. The main theorem follows from
the area upper bound `MovingSofa.areaUpperBound`.
-/

@[expose] public section

namespace MovingSofa

open MeasureTheory

/-- Gerver's sofa attains the sofa constant (Baek, arXiv:2411.19826). -/
theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa := by
  apply optimality_of_areaUpperBound
  exact areaUpperBound

end MovingSofa
