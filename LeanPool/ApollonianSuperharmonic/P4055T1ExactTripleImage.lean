/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.P4055T1GridPathImage

-- [TABLET NODE: P4055T1ExactTripleImage]

/-!
# P4055T1ExactTripleImage

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4055T1ExactTripleImage
    (f : GaussianInt → GaussianInt) (hf : Function.Injective f)
    (hstep : ∀ a b : GaussianInt,
      (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
      (f b = f a + 1 ∨ f b = f a - 1 ∨
        f b = f a + ⟨0, 1⟩ ∨ f b = f a - ⟨0, 1⟩))
    (A B C A' B' C' : ProtoTile)
    (hvA : FootprintVertices A' = f '' FootprintVertices A)
    (hvB : FootprintVertices B' = f '' FootprintVertices B)
    (hvC : FootprintVertices C' = f '' FootprintVertices C)
    (heA : FootprintEdges A' = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges A)
    (heB : FootprintEdges B' = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges B)
    (heC : FootprintEdges C' = (fun e : Finset GaussianInt => e.image f) '' FootprintEdges C)
    (d : ExactTileInterfaceTriple A B C) :
    ∃ d' : ExactTileInterfaceTriple A' B' C',
      d'.point = f d.point ∧ d'.otherAB = f d.otherAB ∧
      d'.otherBC = f d.otherBC ∧ d'.otherCA = f d.otherCA := by
-- BODY
  have hei : Function.Injective (fun e : Finset GaussianInt => e.image f) :=
    Finset.image_injective hf
  have pathAB := P4055T1GridPathImage f hf hstep _ _ _ _ d.pathAB
  have pathBC := P4055T1GridPathImage f hf hstep _ _ _ _ d.pathBC
  have pathCA := P4055T1GridPathImage f hf hstep _ _ _ _ d.pathCA
  have hab : SimpleGridPathBetween
      (FootprintVertices A' ∩ FootprintVertices B')
      (FootprintEdges A' ∩ FootprintEdges B') (f d.point) (f d.otherAB) := by
    simpa only [hvA, hvB, heA, heB, Set.image_inter hf, Set.image_inter hei] using pathAB
  have hbc : SimpleGridPathBetween
      (FootprintVertices B' ∩ FootprintVertices C')
      (FootprintEdges B' ∩ FootprintEdges C') (f d.point) (f d.otherBC) := by
    simpa only [hvB, hvC, heB, heC, Set.image_inter hf, Set.image_inter hei] using pathBC
  have hca : SimpleGridPathBetween
      (FootprintVertices C' ∩ FootprintVertices A')
      (FootprintEdges C' ∩ FootprintEdges A') (f d.point) (f d.otherCA) := by
    simpa only [hvC, hvA, heC, heA, Set.image_inter hf, Set.image_inter hei] using pathCA
  have hu : ∀ z,
      z ∈ FootprintVertices A' ∩ FootprintVertices B' ∩ FootprintVertices C' ↔
        z = f d.point := by
    intro z
    rw [hvA, hvB, hvC, ← Set.image_inter hf, ← Set.image_inter hf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact congrArg f ((d.unique_common w).mp hw)
    · rintro rfl
      exact ⟨d.point, (d.unique_common d.point).mpr rfl, rfl⟩
  exact ⟨⟨f d.point, f d.otherAB, f d.otherBC, f d.otherCA,
    hab, hbc, hca, hu⟩, rfl, rfl, rfl, rfl⟩

end ApollonianSuperharmonic

end
