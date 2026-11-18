/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4994T6UnitCoordinates
public import LeanPool.ApollonianSuperharmonic.P4994T6Rotation
public import LeanPool.ApollonianSuperharmonic.UnitTriangularStep

-- [TABLET NODE: P4994T6UnitChartRotation]

/-!
# P4994T6UnitChartRotation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4994T6UnitChartRotation (orientation : Bool) (e f : GaussianInt)
    (hdet : 0 < e.re * f.im - e.im * f.re)
    (he : UnitTriangularStep orientation e)
    (hf : UnitTriangularStep orientation f)
    (hsum : UnitTriangularStep orientation (e + f)) :
    ∃ m < 6, ∀ p : Int × Int,
      P4994T6UnitCoordinates orientation
        ((p.1 : GaussianInt) * e + (p.2 : GaussianInt) * f) =
      P4994T6Rotation m p := by
-- BODY
  cases orientation <;>
    simp only [UnitTriangularStep, Bool.false_eq_true, ↓reduceIte,
      Finset.mem_insert, Finset.mem_singleton] at he hf hsum <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try norm_num at hdet
  all_goals try norm_num [Zsqrtd.ext_iff] at hsum
  all_goals first
    | refine ⟨0, by decide, ?_⟩
      intro p; ext <;> simp [P4994T6UnitCoordinates, P4994T6Rotation] <;> omega
    | refine ⟨1, by decide, ?_⟩
      intro p; ext <;> simp [P4994T6UnitCoordinates, P4994T6Rotation] <;> omega
    | refine ⟨2, by decide, ?_⟩
      intro p; ext <;> simp [P4994T6UnitCoordinates, P4994T6Rotation] <;> omega
    | refine ⟨3, by decide, ?_⟩
      intro p; ext <;> simp [P4994T6UnitCoordinates, P4994T6Rotation] <;> omega
    | refine ⟨4, by decide, ?_⟩
      intro p; ext <;> simp [P4994T6UnitCoordinates, P4994T6Rotation] <;> omega
    | refine ⟨5, by decide, ?_⟩
      intro p; ext <;> simp [P4994T6UnitCoordinates, P4994T6Rotation]; omega

end ApollonianSuperharmonic

end
