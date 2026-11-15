/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.NoCheckerboardCellVertex
public import LeanPool.ApollonianSuperharmonic.P3475T1BoundaryReduction
public import LeanPool.ApollonianSuperharmonic.P3475T1BoundaryRestoration
public import LeanPool.ApollonianSuperharmonic.P3475T1GridBoundary
public import LeanPool.ApollonianSuperharmonic.P3475T1PolygonTriangleConstruction
public import LeanPool.ApollonianSuperharmonic.P3475T1PolygonalSeparation
public import LeanPool.ApollonianSuperharmonic.P3475T1SquareUnionIdentification

/-!
# Finite polyomino paired triangulation

The boundary reduction, polygonal separation and boundary restoration shared by
the disk criterion and the affine paired-model construction.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FinitePolyominoPairedTriangulation (T : ProtoTile)
    (hinside : FourNeighborConnected (T.cells : Set LatticeCell))
    (houtside : FourNeighborConnected ((T.cells : Set LatticeCell)ᶜ))
    (hchecker : NoCheckerboardCellVertex (T.cells : Set LatticeCell)) :
    ∃ (n : Nat) (p : P3381T1PolygonBoundary n)
      (v : Fin (n + 3) → GaussianInt) (K : Set (Real × Real)),
      Nonempty (P3381T1PairedTriangulation p (TileRealization T) K) ∧
      (∀ i, p.vertex i = GaussianRealPoint (v i)) ∧
      BoundaryFootprintEdges T = {e | ∃ i, e = {v i, v (i + 1)}} := by
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
  exact ⟨n, p, v, K, ⟨t⟩, hvertex, hedges⟩

end ApollonianSuperharmonic

end
