/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4793T1PatchSeparators
public import LeanPool.ApollonianSuperharmonic.P4793T1SeparatorIntersection
public import LeanPool.ApollonianSuperharmonic.P4715T1PositionInjective

-- [TABLET NODE: P4793T1PatchIntersections]

/-!
# P4793T1PatchIntersections

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4793T1PatchIntersections (i j : Fin 12) (hij : i ≠ j) :
    let V := fun j : Fin 12 => Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))
    convexHull Real (P4715T1Position '' V i) ∩
      convexHull Real (P4715T1Position '' V j) =
      convexHull Real (P4715T1Position '' (V i ∩ V j)) := by
-- BODY
  let V := fun j : Fin 12 => Set.range (SixSubtileFaceVertices (P4715T1PatchFaces j))
  have ordered (i j : Fin 12) (hij : i < j) :
      convexHull Real (P4715T1Position '' V i) ∩
        convexHull Real (P4715T1Position '' V j) =
        convexHull Real (P4715T1Position '' (V i ∩ V j)) := by
    obtain ⟨a, b, c, hS, hT, hface⟩ := P4793T1PatchSeparators i j hij
    let f : (Real × Real) →ᵃ[Real] Real :=
      { toFun := fun z => (a : Real)*(12*z.1)+(b : Real)*(12*z.2)+(c : Real)
        linear :=
          { toFun := fun z => (a : Real)*(12*z.1)+(b : Real)*(12*z.2)
            map_add' := by intros; simp; ring
            map_smul' := by intros; simp; ring }
        map_vadd' := by intros; simp; ring }
    have heq := P4793T1SeparatorIntersection
      (P4715T1Position '' V i) (P4715T1Position '' V j) f
      (by rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩; exact hS k)
      (by rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩; exact hT k) (by
        rcases hface with hface | hface
        · left
          rintro _ ⟨⟨_, ⟨k, rfl⟩, rfl⟩, hz⟩
          obtain ⟨l, hl⟩ := hface k hz
          exact ⟨_, ⟨l, rfl⟩, hl.symm⟩
        · right
          rintro _ ⟨⟨_, ⟨k, rfl⟩, rfl⟩, hz⟩
          obtain ⟨l, hl⟩ := hface k hz
          exact ⟨_, ⟨l, rfl⟩, hl.symm⟩)
    rw [heq, Set.image_inter P4715T1PositionInjective]
  dsimp only
  rcases lt_or_gt_of_ne hij with h | h
  · exact ordered i j h
  · simpa only [Set.inter_comm] using ordered j i h

end ApollonianSuperharmonic

end
