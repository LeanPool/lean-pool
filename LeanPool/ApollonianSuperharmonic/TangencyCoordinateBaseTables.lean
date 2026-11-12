/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateNormLaw
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinatePolarizationLaw


-- [TABLET NODE: TangencyCoordinateBaseTables]

/-!
# TangencyCoordinateBaseTables

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TangencyCoordinateBaseTables (z : GaussianInt) :
    TangencyCoordinateNormLaw
        ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩),
          (0, 1), (0, -1)] ∧
      TangencyCoordinatePolarizationLaw
        ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩),
          (0, 1), (0, -1)] := by
-- BODY
  constructor
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [Zsqrtd.norm]
  · intro a b j hab haj hbj
    fin_cases a <;> fin_cases b <;> fin_cases j <;>
      simp_all

end ApollonianSuperharmonic

end
