/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5455T2CurvatureGrowth
public import LeanPool.ApollonianSuperharmonic.P5455T2OccurrenceRotation
public import LeanPool.ApollonianSuperharmonic.P4828T1LeftRootGeometry

-- [TABLET NODE: P5455T2LeftRegressions]

/-!
# P5455T2LeftRegressions

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5455T2LeftRegressions (z : GaussianInt) :
    let q : Fin 4 → CircleCoordinates :=
      ![(12, 7 + 24 * z + 12 * ⟨0, 1⟩),
        (4, 1 + 8 * z + 4 * ⟨0, 1⟩),
        (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (1, 1 + 2 * z)]
    let q' : Fin 4 → CircleCoordinates :=
      ![(24, 17 + 48 * z + 24 * ⟨0, 1⟩),
        (12, 7 + 24 * z + 12 * ⟨0, 1⟩),
        (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (1, 1 + 2 * z)]
    ProperBandQuadruple q ∧ PrimitiveVectorOrientation (q 2) (q 3) ∧
      UnitOccurrenceOrientation q 1 false ∧ UnitOccurrenceOrientation q 2 true ∧
      ProperBandQuadruple q' ∧ PrimitiveVectorOrientation (q' 2) (q' 3) ∧
      UnitOccurrenceOrientation q' 1 false ∧ UnitOccurrenceOrientation q' 2 true := by
-- BODY
  dsimp only
  let L := P4828T1Root z false
  let p : Fin 4 → CircleCoordinates := ![L 0, L 2, L 3, L 1]
  let q : Fin 4 → CircleCoordinates :=
    ![(12, 7 + 24 * z + 12 * ⟨0, 1⟩),
      (4, 1 + 8 * z + 4 * ⟨0, 1⟩),
      (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (1, 1 + 2 * z)]
  have hp : ProperBandQuadruple p := by
    convert P4828T1RotationLaws.2.2 L 1 (P4828T1LeftRootGeometry z).1 using 1
    funext k
    fin_cases k <;> rfl
  have oldB : UnitOccurrenceOrientation p 1 false := by
    have h := (P5455T2OccurrenceRotation L 2 1 false).mpr
      (UnitOccurrenceOrientation.leftUpper z)
    convert h using 1
    · funext k
      fin_cases k <;> rfl
    · decide +kernel
  have oldD : UnitOccurrenceOrientation p 2 true := by
    have h := (P5455T2OccurrenceRotation L 0 1 true).mpr
      (UnitOccurrenceOrientation.leftLower z)
    convert h using 1
    · funext k
      fin_cases k <;> rfl
    · decide +kernel
  have eq : P4828T1Step p = q := by
    funext k
    fin_cases k <;> simp [P4828T1Step, p, L, P4828T1Root, q]; ring
  have direction : PrimitiveVectorOrientation (p 2) (p 3) := .base10 z
  have hq : ProperBandQuadruple q := eq ▸ (P5455T2CurvatureGrowth p hp).2.1
  have hB : UnitOccurrenceOrientation q 1 false := by
    rw [← eq]
    exact .retainSecondToThird hp rfl direction oldB
  have hD : UnitOccurrenceOrientation q 2 true := by
    rw [← eq]
    exact .retainThirdFromSecond hp rfl direction oldD
  have eq' : P4828T1Step q =
      ![(24, 17 + 48 * z + 24 * ⟨0, 1⟩),
        (12, 7 + 24 * z + 12 * ⟨0, 1⟩),
        (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (1, 1 + 2 * z)] := by
    funext k
    fin_cases k <;> simp [P4828T1Step, q]; ring
  refine ⟨hq, PrimitiveVectorOrientation.base10 z, hB, hD, ?_,
    PrimitiveVectorOrientation.base10 z, ?_, ?_⟩
  · rw [← eq']
    exact (P5455T2CurvatureGrowth q hq).2.1
  · rw [← eq']
    exact .retainSecondToThird hq rfl (.base10 z) hB
  · rw [← eq']
    exact .retainThirdFromSecond hq rfl (.base10 z) hD

end ApollonianSuperharmonic

end
