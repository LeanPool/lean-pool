/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5455T2OccurrenceExists
public import LeanPool.ApollonianSuperharmonic.P5455T2OccurrenceDeterministic
public import LeanPool.ApollonianSuperharmonic.P5455T2LeftRegressions
public import LeanPool.ApollonianSuperharmonic.P5455T2RightRegressions
public import LeanPool.ApollonianSuperharmonic.P5455T2WholeJoin

-- [TABLET NODE: UnitOccurrenceOrientationUnique]

/-!
# UnitOccurrenceOrientationUnique

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem UnitOccurrenceOrientationUnique :
    (∀ (q : Fin 4 → CircleCoordinates), ProperBandQuadruple q →
      ∀ i : Fin 3, (q i.succ).1 = 1 →
        ∃! orientation : Bool,
          UnitOccurrenceOrientation q i orientation) ∧
    ∀ z : GaussianInt,
      let qLeft : Fin 4 → CircleCoordinates :=
        ![(12, 7 + 24 * z + 12 * ⟨0, 1⟩),
          (4, 1 + 8 * z + 4 * ⟨0, 1⟩),
          (1, 1 + 2 * z + 2 * ⟨0, 1⟩),
          (1, 1 + 2 * z)]
      let qRight : Fin 4 → CircleCoordinates :=
        ![(12, 17 + 24 * z + 12 * ⟨0, 1⟩),
          (4, 7 + 8 * z + 4 * ⟨0, 1⟩),
          (1, 1 + 2 * z),
          (1, 1 + 2 * z + 2 * ⟨0, 1⟩)]
      let qLeftRepeat : Fin 4 → CircleCoordinates :=
        ![(24, 17 + 48 * z + 24 * ⟨0, 1⟩),
          (12, 7 + 24 * z + 12 * ⟨0, 1⟩),
          (1, 1 + 2 * z + 2 * ⟨0, 1⟩),
          (1, 1 + 2 * z)]
      let qRightRepeat : Fin 4 → CircleCoordinates :=
        ![(24, 31 + 48 * z + 24 * ⟨0, 1⟩),
          (12, 17 + 24 * z + 12 * ⟨0, 1⟩),
          (1, 1 + 2 * z),
          (1, 1 + 2 * z + 2 * ⟨0, 1⟩)]
      let v := BandVectors.1 (qLeft 1) (qLeft 3)
      ProperBandQuadruple qLeft ∧
        PrimitiveVectorOrientation (qLeft 2) (qLeft 3) ∧
        UnitOccurrenceOrientation qLeft 1 false ∧
        UnitOccurrenceOrientation qLeft 2 true ∧
        ProperBandQuadruple qRight ∧
        PrimitiveVectorOrientation (qRight 3) (qRight 2) ∧
        UnitOccurrenceOrientation qRight 1 true ∧
        UnitOccurrenceOrientation qRight 2 false ∧
        ProperBandQuadruple qLeftRepeat ∧
        PrimitiveVectorOrientation (qLeftRepeat 2) (qLeftRepeat 3) ∧
        UnitOccurrenceOrientation qLeftRepeat 1 false ∧
        UnitOccurrenceOrientation qLeftRepeat 2 true ∧
        ProperBandQuadruple qRightRepeat ∧
        PrimitiveVectorOrientation (qRightRepeat 3) (qRightRepeat 2) ∧
        UnitOccurrenceOrientation qRightRepeat 1 true ∧
        UnitOccurrenceOrientation qRightRepeat 2 false ∧
        v.re * v.re + v.im * v.im = 5 ∧
        ∀ orientation : Bool, ¬ UnitTriangularStep orientation v := by
-- BODY
  constructor
  · intro q hq i hi
    obtain ⟨o, ho⟩ := P5455T2OccurrenceExists q hq i hi
    refine ⟨o, ho, ?_⟩
    intro o' ho'
    exact P5455T2OccurrenceDeterministic q hq i hi o' o ho' ho
  · intro z
    dsimp only
    obtain ⟨hl, hld, hl1, hl2, hll, hlld, hll1, hll2⟩ :=
      P5455T2LeftRegressions z
    obtain ⟨hr, hrd, hr1, hr2, hrr, hrrd, hrr1, hrr2⟩ :=
      P5455T2RightRegressions z
    have join := P5455T2WholeJoin z
    exact ⟨hl, hld, hl1, hl2, hr, hrd, hr1, hr2,
      hll, hlld, hll1, hll2, hrr, hrrd, hrr1, hrr2, join.1, join.2⟩

end ApollonianSuperharmonic

end
