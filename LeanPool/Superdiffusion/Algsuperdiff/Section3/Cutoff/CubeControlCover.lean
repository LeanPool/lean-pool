/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CubeControlTransport

/-!
# CubeControlCover

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Local controls on translated unit cubes

The finite-cover tail argument uses these exact translated unit-cube controls.
-/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport Set
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The exact value control on the open unit cube translated by `z`. -/
def translatedUnitCubeControl (z : Vec d) (j : ShellField d) : ℝ :=
  ShellField.unitCubeValueNorm (ShellField.translate z j)

theorem translatedUnitCubeControl_nonneg (z : Vec d) (j : ShellField d) :
    0 ≤ translatedUnitCubeControl z j :=
  ShellField.unitCubeValueNorm_nonneg _

theorem measurable_translatedUnitCubeControl (z : Vec d) :
    Measurable (translatedUnitCubeControl (d := d) z) :=
  ShellField.unitCubeValueNorm_measurable.comp (ShellField.measurable_translate z)

/-- The translated unit control bounds the matrix operator norm on its literal
open translated cube. -/
theorem matrixOperatorNorm_le_translatedUnitCubeControl
    (z : Vec d) (j : ShellField d) {x : Vec d}
    (hx : x ∈ translateSet z (openCubeSet (originCube d 0))) :
    HCPolySupport.Book.Ch02.matrixOperatorNorm (j x) ≤
      translatedUnitCubeControl z j := by
  rw [mem_translateSet_iff_sub_mem] at hx
  let y : ShellField.UnitOpenCubePoint d := ⟨x - z, hx⟩
  have h := ShellField.matrixOperatorNorm_apply_le_unitCubeValueNorm
    (ShellField.translate z j) y
  simpa [translatedUnitCubeControl, y, ShellField.translate_apply,
    sub_add_cancel] using h

end

end Algsuperdiff.Section3.Cutoff
