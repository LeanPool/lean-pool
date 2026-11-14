/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Analysis.Convex.GaugeRescale
public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.NoCheckerboardCellVertex
public import LeanPool.ApollonianSuperharmonic.P3475T1BoundaryReduction
public import LeanPool.ApollonianSuperharmonic.P3475T1BoundaryRestoration
public import LeanPool.ApollonianSuperharmonic.P3475T1GridBoundary
public import LeanPool.ApollonianSuperharmonic.P3475T1PolygonTriangleConstruction
public import LeanPool.ApollonianSuperharmonic.P3475T1PolygonalSeparation
public import LeanPool.ApollonianSuperharmonic.P3475T1SquareUnionIdentification

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
  obtain ⟨n, p, v, hvertex, _hadj, _hvertices, hedges⟩ :=
    P3475T1GridBoundary T hinside houtside hchecker
  obtain ⟨r, q, ⟨s⟩, hcorner⟩ := P3475T1BoundaryReduction p
  obtain ⟨X, K, ⟨tree⟩⟩ := P3475T1PolygonTriangleConstruction q hcorner
  obtain ⟨U, V, hUopen, hUconn, hUb, hVopen, hVconn, hVub,
    hdisj, hcover, hfrontU, hfrontV, hX⟩ :=
      P3475T1PolygonalSeparation q X K tree
  have hcoverP : U ∪ V =
      (⋃ i, segment Real (p.vertex i) (p.vertex (i + 1)))ᶜ := by
    rw [s.carrier_eq]
    exact hcover
  have hfrontUP : frontier U =
      ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1)) :=
    hfrontU.trans s.carrier_eq.symm
  have hfrontVP : frontier V =
      ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1)) :=
    hfrontV.trans s.carrier_eq.symm
  have htile := P3475T1SquareUnionIdentification T hinside houtside
    p v hvertex hedges U V hUopen hUconn hUb hVopen hVconn hVub
    hdisj hcoverP hfrontUP hfrontVP
  have hsource : X = TileRealization T := by
    rw [htile, s.carrier_eq]
    exact hX
  obtain ⟨t⟩ := P3475T1BoundaryRestoration q p s X K tree
  rw [hsource] at t
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
