/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4715T1Hexagon
public import LeanPool.ApollonianSuperharmonic.P4715T1PatchFaces
public import LeanPool.ApollonianSuperharmonic.SixSubtileFaceVertices
public import LeanPool.ApollonianSuperharmonic.P4783T1PatchDeterminants
public import LeanPool.ApollonianSuperharmonic.P4793T1PatchIntersections
public import LeanPool.ApollonianSuperharmonic.P4793T1PatchBoundaryTraces

-- [TABLET NODE: P4715T1HexagonSubdivision]

/-!
# P4715T1HexagonSubdivision

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4715T1HexagonSubdivision :
    let V := fun j : Fin 12 => Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))
    let K := fun j : Fin 12 => convexHull Real (P4715T1Position '' V j)
    (⋃ j, K j) = P4715T1Hexagon ∧
    (∀ j : Fin 12,
      let p := P4715T1Position ∘ SixSubtileFaceVertices (P4715T1PatchFaces j)
      (p 1).1 * (p 2).2 - (p 1).1 * (p 0).2 -
        (p 0).1 * (p 2).2 - (p 1).2 * (p 2).1 +
        (p 1).2 * (p 0).1 + (p 0).2 * (p 2).1 ≠ 0) ∧
    (∀ i j : Fin 12, i ≠ j →
      K i ∩ K j = convexHull Real (P4715T1Position '' (V i ∩ V j))) ∧
    ∀ j : Fin 12, K j ∩ frontier P4715T1Hexagon =
      convexHull Real (P4715T1Position ''
        (V j ∩ Set.range P4715T1BoundaryCycle)) := by
-- BODY
  dsimp only
  refine ⟨P4783T1PatchCoverage, P4783T1PatchDeterminants, ?_, ?_⟩
  · intro i j hij
    exact P4793T1PatchIntersections i j hij
  · intro j
    exact P4793T1PatchBoundaryTraces j

end ApollonianSuperharmonic

end
