/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure

/-!
# High-contrast homogenization: Provider.Regularity.CubeVolume

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Cube volumes are nonzero and finite

The two corollaries of the exact cube-volume formula that every domain-change
estimate on a triadic cube needs: an open cube has volume neither `0` nor `⊤`.
Both follow at once from `volume_openCubeSet_toReal` and the positivity of the
cube's scale factor.  They are collected here so that the estimates consuming
them share one statement instead of repeating the argument.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

variable {d : ℕ}

/-- An open triadic cube has nonzero volume. -/
theorem volume_openCubeSet_ne_zero (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ 0 := by
  have hreal : (volume (openCubeSet Q)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  exact (ENNReal.toReal_ne_zero.mp hreal).1

/-- An open triadic cube has finite volume. -/
theorem volume_openCubeSet_ne_top (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ ⊤ :=
  (volume_openCubeSet_lt_top Q).ne

end HighContrast
end HCPolySupport
