/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LatticeTileComplementGridConnected
public import LeanPool.ApollonianSuperharmonic.P3475T1GridBoundary
public import LeanPool.ApollonianSuperharmonic.P3475T1BoundaryReduction
public import LeanPool.ApollonianSuperharmonic.P3475T1PolygonTriangleConstruction
public import LeanPool.ApollonianSuperharmonic.P3475T1PolygonalSeparation
public import LeanPool.ApollonianSuperharmonic.P3475T1SquareUnionIdentification
public import LeanPool.ApollonianSuperharmonic.P3475T1BoundaryRestoration

-- [TABLET NODE: P3723T1GridDiskPairedModel]

/-!
# P3723T1GridDiskPairedModel

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3723T1GridDiskPairedModel (T : ProtoTile) (hT : LatticeTile T) :
    ∃ (n : Nat) (p : P3381T1PolygonBoundary n)
      (v : Fin (n + 3) → GaussianInt) (K : Set (Real × Real))
      (t : P3381T1PairedTriangulation p (TileRealization T) K)
      (h : TileRealization T ≃ₜ K),
      (∀ i, p.vertex i = GaussianRealPoint (v i)) ∧
      BoundaryFootprintEdges T = {e | ∃ i, e = {v i, v (i + 1)}} ∧
      frontier (TileRealization T) =
        ⋃ i, segment Real (p.vertex i) (p.vertex (i + 1)) ∧
      (∀ x : TileRealization T,
        (x : Real × Real) ∈ frontier (TileRealization T) ↔
          (h x : Real × Real) ∈ frontier K) ∧
      (∀ x : TileRealization T,
        (x : Real × Real) ∈ interior (TileRealization T) ↔
          (h x : Real × Real) ∈ interior K) ∧
      ∀ k (x : TileRealization T),
        (x : Real × Real) ∈ convexHull Real (Set.range (p.vertex ∘ t.face k)) →
        ∀ w : Fin 3 → Real, (∑ i, w i) = 1 →
          (x : Real × Real) = ∑ i, w i • p.vertex (t.face k i) →
          (h x : Real × Real) = ∑ i, w i • t.target (t.face k i) := by
-- BODY
  obtain ⟨hinside, hchecker, _hcycle⟩ := LatticeTileGridStructure T hT
  have houtside := LatticeTileComplementGridConnected T hT
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
  obtain ⟨h, hboundary, haffine⟩ :=
    P3381T1PiecewiseAffinePolygonModel p (TileRealization T) K t
  have hfrontier :=
    (P3381T1TriangulationBoundary p (TileRealization T) K t).2.2.1
  refine ⟨n, p, v, K, t, h, hvertex, hedges, hfrontier, hboundary, ?_, haffine⟩
  intro x
  rw [mem_interior_iff_notMem_frontier x.property,
    mem_interior_iff_notMem_frontier (h x).property]
  exact not_congr (hboundary x)

end ApollonianSuperharmonic

end
