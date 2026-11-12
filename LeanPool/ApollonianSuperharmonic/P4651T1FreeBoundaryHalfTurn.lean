/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4590T1CentralDiskSectors
public import LeanPool.ApollonianSuperharmonic.P4397T1ReflectedEdgeNotBoundary
public import LeanPool.ApollonianSuperharmonic.P4456T2VertexInterior
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric

-- [TABLET NODE: P4651T1FreeBoundaryHalfTurn]

/-!
# P4651T1FreeBoundaryHalfTurn

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4651T1FreeBoundaryHalfTurn (O : ProtoTile)
    (hO : O.cells.Nonempty) (hL : LatticeTile O)
    (hQ : QuarterTurnSymmetric O) (w : GaussianInt)
    (hw : GaussianRealPoint w =
      (2 * (TileCentroid O).1, 2 * (TileCentroid O).2))
    (hR : CentrallyReflectedAt (TileCentroid O) O O) :
    (∀ z ∈ BoundaryFootprintVertices O, w - z ≠ z) ∧
    (∀ e ∈ BoundaryFootprintEdges O,
      e.image (fun z => w - z) ≠ e) := by
-- BODY
  classical
  have real_action (z : GaussianInt) : GaussianRealPoint (w - z) =
      (2 * (TileCentroid O).1 - (GaussianRealPoint z).1,
        2 * (TileCentroid O).2 - (GaussianRealPoint z).2) := by
    have hx := congrArg Prod.fst hw
    have hy := congrArg Prod.snd hw
    dsimp [GaussianRealPoint] at hx hy
    change (((w.re - z.re : Int) : Real), ((w.im - z.im : Int) : Real)) = _
    push_cast
    exact Prod.ext (by dsimp [GaussianRealPoint]; linarith)
      (by dsimp [GaussianRealPoint]; linarith)
  have free_vertex : ∀ z ∈ BoundaryFootprintVertices O, w - z ≠ z := by
    intro z hz hfix
    have hh := real_action z
    rw [hfix] at hh
    have hc : TileCentroid O = GaussianRealPoint z := by
      have hx := congrArg Prod.fst hh
      have hy := congrArg Prod.snd hh
      exact Prod.ext (by dsimp at hx ⊢; linarith)
        (by dsimp at hy ⊢; linarith)
    have hall := P4590T1CentralDiskSectors O hL hQ z hc
    have hraw : z ∈ FootprintVertices O := by
      simp only [FootprintVertices, ite_eq_left hO, Set.mem_ofPred_eq]
      exact ⟨z, by simpa [LatticeVertexIncidentCell] using hall 0, Or.inl rfl⟩
    exact ((P4456T2VertexInterior O hO z hraw).2.mpr hall) hz
  refine ⟨free_vertex, ?_⟩
  intro e he hfix
  have impossible (a b : GaussianInt) (hadj : FourNeighborAdjacent a b)
      (he : {a, b} ∈ BoundaryFootprintEdges O)
      (hf : ({a, b} : Finset GaussianInt).image (fun z => w - z) = {a, b}) :
      False := by
    have ha : a ∈ BoundaryFootprintVertices O := by
      simp only [BoundaryFootprintVertices, ite_eq_left hO, Set.mem_ofPred_eq]
      exact ⟨{a, b}, he, by simp⟩
    have hr : w - a = a ∨ w - a = b := by
      have : w - a ∈ ({a, b} : Finset GaussianInt) := by
        rw [← hf]
        exact Finset.mem_image.mpr ⟨a, by simp, rfl⟩
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    rcases hr with hr | hr
    · exact free_vertex a ha hr
    · have hab : GaussianRealPoint b =
          (2 * (TileCentroid O).1 - (GaussianRealPoint a).1,
            2 * (TileCentroid O).2 - (GaussianRealPoint a).2) := by
        rw [← hr]
        exact real_action a
      exact P4397T1ReflectedEdgeNotBoundary O (TileCentroid O) hR a b hadj hab he
  rcases he with ⟨z, ⟨rfl, hz⟩ | ⟨rfl, hz⟩⟩
  · exact impossible z (z + 1) (Or.inl rfl) ⟨z, Or.inl ⟨rfl, hz⟩⟩ hfix
  · exact impossible z (z + ⟨0, 1⟩) (Or.inr (Or.inr (Or.inl rfl)))
      ⟨z, Or.inr ⟨rfl, hz⟩⟩ hfix

end ApollonianSuperharmonic

end
