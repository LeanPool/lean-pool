/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P4994T6UnitRootTable]

/-!
# P4994T6UnitRootTable

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4994T6UnitRootTable (z : GaussianInt) :
    let L := P4828T1Root z false
    let H := P4828T1Root z true
    let I : GaussianInt := ⟨0, 1⟩
    (BandVectors.1 (L 2) (L 1) = -I ∧
      I * BandVectors.1 (L 1) (L 3) = -1 - I) ∧
    (BandVectors.1 (L 1) (L 3) = -1 + I ∧
      I * BandVectors.1 (L 3) (L 2) = I) ∧
    (BandVectors.1 (H 2) (H 1) = 1 + I ∧
      I * BandVectors.1 (H 1) (H 3) = 1) ∧
    (BandVectors.1 (H 3) (H 2) = -1 ∧
      I * BandVectors.1 (H 2) (H 1) = -1 + I) := by
-- BODY
  have system : RecursiveVectorSystem BandVectors := by
    simpa [BandVectors] using (Classical.choose_spec RecursiveVectorsExistUnique).1
  have base := system.2.1 z
  dsimp at base
  have step := system.2.2.1 _ (SemiProperQuadruple.base z)
  dsimp at step
  have plus_lower : BandVectors.1 (0, 1) (1, 1 + 2 * z) = -1 := by
    simpa [base.1, base.2.1] using step.1
  have lower_minus : BandVectors.1 (1, 1 + 2 * z) (0, -1) = 1 := by
    simpa [base.1, base.2.2.1] using step.2.1
  have upper_lower : BandVectors.1 (1, 1 + 2 * z + 2 * ⟨0, 1⟩)
      (1, 1 + 2 * z) = 1 + (⟨0, 1⟩ : GaussianInt) := by
    have h := (VectorRecursionLaws _ (SemiProperQuadruple.base z)).2.2.1
    simpa [base.2.1, base.2.2.1] using h
  have lower_upper : BandVectors.1 (1, 1 + 2 * z)
      (1, 1 + 2 * z + 2 * ⟨0, 1⟩) = -1 + (⟨0, 1⟩ : GaussianInt) := by
    have h := (system.2.2.2 _ _ (PrimitiveVectorOrientation.base10 z)).1
    rw [upper_lower] at h
    convert h using 1; ext <;> simp
  have shift : (1, 1 + 2 * (z - (⟨0, 1⟩ : GaussianInt)) + 2 * ⟨0, 1⟩) =
      ((1, 1 + 2 * z) : CircleCoordinates) := by
    congr 1
    ring
  have lower_plus : BandVectors.1 (1, 1 + 2 * z) (0, 1) =
      -(⟨0, 1⟩ : GaussianInt) := by
    have h := (system.2.2.2 _ _
      (PrimitiveVectorOrientation.base21 (z - (⟨0, 1⟩ : GaussianInt)))).1
    rw [shift, plus_lower] at h
    simpa using h
  have minus_lower : BandVectors.1 (0, -1) (1, 1 + 2 * z) =
      -(⟨0, 1⟩ : GaussianInt) := by
    have h := (system.2.2.2 _ _
      (PrimitiveVectorOrientation.base31 (z - (⟨0, 1⟩ : GaussianInt)))).1
    rw [shift, lower_minus] at h
    have hre := congrArg (fun w : GaussianInt => w.re) h
    have him := congrArg (fun w : GaussianInt => w.im) h
    simp at hre him
    ext <;> simp <;> omega
  dsimp [P4828T1Root]
  simp only [minus_lower, lower_upper, upper_lower, lower_plus, base.2.1, base.2.2.1]
  norm_num [Zsqrtd.ext_iff]

end ApollonianSuperharmonic

end
