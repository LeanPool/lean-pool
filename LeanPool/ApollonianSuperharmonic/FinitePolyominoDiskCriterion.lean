/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.P3381T1PiecewiseAffinePolygonModel
public import LeanPool.ApollonianSuperharmonic.FinitePolyominoPairedTriangulation

public import Mathlib.Analysis.Convex.GaugeRescale
public import LeanPool.ApollonianSuperharmonic.LatticeTile

-- [TABLET NODE: FinitePolyominoDiskCriterion]

/-!
# FinitePolyominoDiskCriterion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FinitePolyominoDiskCriterion (T : ProtoTile)
    (hinside : FourNeighborConnected (T.cells : Set LatticeCell))
    (houtside : FourNeighborConnected ((T.cells : Set LatticeCell)ᶜ))
    (hchecker : NoCheckerboardCellVertex (T.cells : Set LatticeCell)) :
    LatticeTile T := by
-- BODY
  obtain ⟨_, p, _, K, ⟨t⟩, _, _⟩ :=
    FinitePolyominoPairedTriangulation T hinside houtside hchecker
  obtain ⟨h, _hboundary, _haffine⟩ :=
    P3381T1PiecewiseAffinePolygonModel p (TileRealization T) K t
  obtain ⟨H, _hinterior, hclosure, _hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      t.target_convex t.target_interior t.target_bounded
  have hK : H '' K = Metric.closedBall 0 1 := by
    simpa only [t.target_closed.closure_eq] using hclosure
  let model : K ≃ₜ (Metric.closedBall (0 : Real × Real) 1 : Set (Real × Real)) :=
    (H.image K).trans (Homeomorph.setCongr hK)
  exact ⟨model.symm.trans h.symm⟩

end ApollonianSuperharmonic

end
