/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondRecursiveQuadruple
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance

-- [TABLET NODE: P4564T2DiamondOrderExclusion]

/-!
# P4564T2DiamondOrderExclusion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4564T2DiamondOrderExclusion :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (a : Fin 3), ∀ (g : BandPackingSymmetry), ∀ (K :
        DiamondParameter), (BandPackingSymmetryQuadrupleAction g ![q 0, q a.succ, q (a + 1).succ,
        q (a +
        2).succ] =
      DiamondRecursiveQuadruple K) → (((q 2).1 ≤ (q 1).1) → (((q 3).1 ≤ (q 2).1) → ((q 2).1 ≤
          1))) := by
  intro q a g K hnormal h12 h23
-- BODY
  have h1 := congrArg (fun p : Fin 4 → CircleCoordinates => (p 1).1) hnormal
  have h2 := congrArg (fun p : Fin 4 → CircleCoordinates => (p 2).1) hnormal
  have hc := (BandPackingSymmetryCovariance g).1
  cases ho : BandPackingSymmetryReversesOrientation g <;> fin_cases a <;>
    simp [BandPackingSymmetryQuadrupleAction, ho, hc,
      DiamondRecursiveQuadruple] at h1 h2 <;> omega

end ApollonianSuperharmonic

end
