/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryQuadrupleAction

-- [TABLET NODE: P4840T6ConstructorCovariance]

/-!
# P4840T6ConstructorCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4840T6ConstructorCovariance (g : BandPackingSymmetry)
    (hg : ∃ w : GaussianInt, g = .shift w ∨ g = .comp (.shift w) .negate) :
    BandPackingSymmetryReversesOrientation g = false ∧
    (∀ C : CircleCoordinates, (BandPackingSymmetryCircleAction g C).1 = C.1) ∧
    ∀ q : Fin 4 → CircleCoordinates,
      let S := fun x : Fin 4 → CircleCoordinates =>
        ![(2 * (x 0).1 + 2 * (x 2).1 + 2 * (x 3).1 - (x 1).1,
            2 * (x 0).2 + 2 * (x 2).2 + 2 * (x 3).2 - (x 1).2),
          x 0, x 2, x 3]
      BandPackingSymmetryQuadrupleAction g (S q) =
        S (BandPackingSymmetryQuadrupleAction g q) := by
  obtain ⟨w, rfl | rfl⟩ := hg
  all_goals
    refine ⟨rfl, (fun _ => rfl), ?_⟩
    intro q
    funext j
    fin_cases j <;> apply Prod.ext
    all_goals simp [BandPackingSymmetryQuadrupleAction, BandPackingSymmetryCircleAction,
      BandPackingSymmetryReversesOrientation]
    all_goals ring

end ApollonianSuperharmonic

end
