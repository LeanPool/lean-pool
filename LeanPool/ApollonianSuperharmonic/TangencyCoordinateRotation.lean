/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateNormLaw
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinatePolarizationLaw


-- [TABLET NODE: TangencyCoordinateRotation]

/-!
# TangencyCoordinateRotation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TangencyCoordinateRotation (q : Fin 4 → CircleCoordinates)
    (hn : TangencyCoordinateNormLaw q)
    (hp : TangencyCoordinatePolarizationLaw q) :
    TangencyCoordinateNormLaw ![q 0, q 2, q 3, q 1] ∧
      TangencyCoordinatePolarizationLaw ![q 0, q 2, q 3, q 1] := by
-- BODY
  constructor
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [TangencyCoordinateNormLaw]
  · intro a b j hab haj hbj
    fin_cases a <;> fin_cases b <;> fin_cases j <;>
      simp_all [TangencyCoordinatePolarizationLaw]

end ApollonianSuperharmonic

end
