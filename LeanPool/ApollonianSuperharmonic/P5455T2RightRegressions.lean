/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5455T2CurvatureGrowth
public import LeanPool.ApollonianSuperharmonic.P5455T2OccurrenceRotation
public import LeanPool.ApollonianSuperharmonic.P4828T1RightRootGeometry

-- [TABLET NODE: P5455T2RightRegressions]

/-!
# P5455T2RightRegressions

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5455T2RightRegressions (z : GaussianInt) :
    let q : Fin 4 → CircleCoordinates :=
      ![(12, 17 + 24 * z + 12 * ⟨0, 1⟩),
        (4, 7 + 8 * z + 4 * ⟨0, 1⟩),
        (1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩)]
    let q' : Fin 4 → CircleCoordinates :=
      ![(24, 31 + 48 * z + 24 * ⟨0, 1⟩),
        (12, 17 + 24 * z + 12 * ⟨0, 1⟩),
        (1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩)]
    ProperBandQuadruple q ∧ PrimitiveVectorOrientation (q 3) (q 2) ∧
      UnitOccurrenceOrientation q 1 true ∧ UnitOccurrenceOrientation q 2 false ∧
      ProperBandQuadruple q' ∧ PrimitiveVectorOrientation (q' 3) (q' 2) ∧
      UnitOccurrenceOrientation q' 1 true ∧ UnitOccurrenceOrientation q' 2 false := by
-- BODY
  dsimp only
  let H := P4828T1Root z true
  let p : Fin 4 → CircleCoordinates := ![H 0, H 3, H 1, H 2]
  let q : Fin 4 → CircleCoordinates :=
    ![(12, 17 + 24 * z + 12 * ⟨0, 1⟩),
      (4, 7 + 8 * z + 4 * ⟨0, 1⟩),
      (1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩)]
  have hp : ProperBandQuadruple p := by
    convert P4828T1RotationLaws.2.2 H 2 (P4828T1RightRootGeometry z).1 using 1
    funext k
    fin_cases k <;> rfl
  have oldB : UnitOccurrenceOrientation p 1 true := by
    have h := (P5455T2OccurrenceRotation H 0 2 true).mpr
      (UnitOccurrenceOrientation.rightUpper z)
    convert h using 1
    · funext k
      fin_cases k <;> rfl
    · decide +kernel
  have oldD : UnitOccurrenceOrientation p 2 false := by
    have h := (P5455T2OccurrenceRotation H 1 2 false).mpr
      (UnitOccurrenceOrientation.rightLower z)
    convert h using 1
    · funext k
      fin_cases k <;> rfl
    · decide +kernel
  have eq : P4828T1Step p = q := by
    funext k
    fin_cases k <;> simp [P4828T1Step, p, H, P4828T1Root, q]; ring
  have direction : PrimitiveVectorOrientation (p 3) (p 2) := .base10 z
  have hq : ProperBandQuadruple q := eq ▸ (P5455T2CurvatureGrowth p hp).2.1
  have hB : UnitOccurrenceOrientation q 1 true := by
    rw [← eq]
    exact .retainSecondFromThird hp rfl direction oldB
  have hD : UnitOccurrenceOrientation q 2 false := by
    rw [← eq]
    exact .retainThirdToSecond hp rfl direction oldD
  have eq' : P4828T1Step q =
      ![(24, 31 + 48 * z + 24 * ⟨0, 1⟩),
        (12, 17 + 24 * z + 12 * ⟨0, 1⟩),
        (1, 1 + 2 * z), (1, 1 + 2 * z + 2 * ⟨0, 1⟩)] := by
    funext k
    fin_cases k <;> simp [P4828T1Step, q]; ring
  refine ⟨hq, PrimitiveVectorOrientation.base10 z, hB, hD, ?_,
    PrimitiveVectorOrientation.base10 z, ?_, ?_⟩
  · rw [← eq']
    exact (P5455T2CurvatureGrowth q hq).2.1
  · rw [← eq']
    exact .retainSecondFromThird hq rfl (.base10 z) hB
  · rw [← eq']
    exact .retainThirdToSecond hq rfl (.base10 z) hD

end ApollonianSuperharmonic

end
