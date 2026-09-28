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

The imported development proves uniqueness of Gerver's defining parameters in
`MovingSofa.GerversSofa.ABφθSpec.existsUnique` and admissibility of the resulting shape in
`MovingSofa.isMovingSofa_gerversSofa`. The main theorem combines this admissibility result
with the proved area upper bound `MovingSofa.areaUpperBound`.
-/

@[expose] public section

namespace MovingSofa

open MeasureTheory

/-- Gerver's sofa attains the sofa constant (Baek, arXiv:2411.19826). -/
theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa := by
  apply optimality_of_areaUpperBound
  exact areaUpperBound

end MovingSofa
