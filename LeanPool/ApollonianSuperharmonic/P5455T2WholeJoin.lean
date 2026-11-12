/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4994T6UnitRootTable
public import LeanPool.ApollonianSuperharmonic.UnitTriangularStep

-- [TABLET NODE: P5455T2WholeJoin]

/-!
# P5455T2WholeJoin

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5455T2WholeJoin (z : GaussianInt) :
    let v := BandVectors.1 (4, 1 + 8 * z + 4 * ⟨0, 1⟩) (1, 1 + 2 * z)
    v.re * v.re + v.im * v.im = 5 ∧
      ∀ o : Bool, ¬ UnitTriangularStep o v := by
-- BODY
  let L := P4828T1Root z false
  have proper := (P4828T1LeftRootGeometry z).1
  have row := P4994T6UnitRootTable z
  have incoming := (VectorRecursionLaws L proper.1).2.2.1
  change BandVectors.1 (L 1) (L 0) = _ at incoming
  rw [show BandVectors.1 (L 1) (L 3) = -1 + (⟨0, 1⟩ : GaussianInt)
      from row.2.1.1,
    show BandVectors.1 (L 2) (L 1) = -(⟨0, 1⟩ : GaussianInt)
      from row.1.1] at incoming
  have flip := ((VectorRecursionLaws L proper.1).2.2.2.2 proper 0).1
  change BandVectors.1 (L 0) (L 1) =
    (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (L 1) (L 0) at flip
  rw [incoming] at flip
  have value : BandVectors.1 (L 0) (L 1) = (-1 - 2 * (⟨0, 1⟩ : GaussianInt)) := by
    rw [flip]
    ext <;> norm_num
  change (BandVectors.1 (L 0) (L 1)).re * (BandVectors.1 (L 0) (L 1)).re +
      (BandVectors.1 (L 0) (L 1)).im * (BandVectors.1 (L 0) (L 1)).im = 5 ∧
        ∀ o, ¬ UnitTriangularStep o (BandVectors.1 (L 0) (L 1))
  rw [value]
  constructor
  · norm_num
  · intro o
    cases o <;> norm_num [UnitTriangularStep, Zsqrtd.ext_iff]

end ApollonianSuperharmonic

end
