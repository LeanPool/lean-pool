/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateBaseTables
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateRotation
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateSuccessorNorm
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateSuccessorPolarization

-- [TABLET NODE: TangencyCoordinateIdentity]

/-!
# TangencyCoordinateIdentity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TangencyCoordinateIdentity (q : Fin 4 → CircleCoordinates)
    (hq : SemiProperQuadruple q) (i j : Fin 4) (hij : i ≠ j) :
    Zsqrtd.norm ((q j).1 • (q i).2 - (q i).1 • (q j).2) =
      ((q i).1 + (q j).1) ^ 2 := by
-- BODY
  have simultaneous : ∀ (r : Fin 4 → CircleCoordinates), SemiProperQuadruple r →
      TangencyCoordinateNormLaw r ∧ TangencyCoordinatePolarizationLaw r := by
    intro r hr
    induction hr with
    | base z => exact TangencyCoordinateBaseTables z
    | rotate hr ih => exact TangencyCoordinateRotation _ ih.1 ih.2
    | successor hr ih =>
        exact ⟨TangencyCoordinateSuccessorNorm _ ih.1 ih.2,
          TangencyCoordinateSuccessorPolarization _ ih.1 ih.2⟩
  exact (simultaneous q hq).1 i j hij

end ApollonianSuperharmonic

end
