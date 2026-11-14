/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: BandOrderedGeneralOdometerRowData]

/-!
# BandOrderedGeneralOdometerRowData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Fix an ordered-general configuration $q$, its layout certificate, a root
support and tile odometer $(T,h)$, literal outer restriction families
$(P_i^s,r_i^s)$, literal positive and negative first-predecessor restriction
families $(Q_i^s,u_i^s)$ and $(S_i^s,v_i^s)$, and an integer lattice
function $g$.  An *ordered-general odometer row datum* consists of the
following simultaneous data.

First, $(T,h)$ is a `TileOdometer` and $T$ is a
`BandPrototile` for $q_0$.  The family $(P,r)$ is the full literal
six-piece decomposition of $(T,h)$: its members are tile odometers for the
three parents of $q$, their cells exactly cover $T$, their footprints lie in
the footprint of $T$, and their centroids have the signed decomposition
offset
$$
 \operatorname{cent}(P_i^s)-\operatorname{cent}(T)={\epsilon_s\over2}(w_i-Jw_i),
 \qquad w_i=\operatorname{BandVectors}.1(q_{i+2},q_{i+1}),
 \quad J(a,b)=(-b,a).
$$
Their domains exactly cover $\operatorname{dom} h$, their values are the restrictions of
$h$, and they are pairwise `OdometerCompatibility`-compatible.  For
each member, either its parent curvature is zero or its slope and the slope
of $h$ exist and differ by
$$
 {\epsilon_s\over2}(\Re b_i-\Im b_i,\Im b_i+\Re b_i),
 \qquad b_i=\operatorname{BandVectors}.2(q_{i+2},q_{i+1}).
$$

Second, $(P_1^+,r_1^+)$ and $(P_1^-,r_1^-)$ are tile odometers and band
prototiles for the child of the first predecessor.  The families $(Q,u)$
and $(S,v)$ are their respective full literal six-piece decompositions.
Each retains the same exact cell cover, footprint inclusions, signed
centroid formulas, exact domain cover, pointwise restriction equations,
within-family compatibility, and zero-curvature-or-defined-slope
alternative just specified, now for the certificate's first predecessor.

Finally, $g$ `GlobalOdometerExtends` every member of all three
function families.  Any two functions drawn from their union are
compatible.  For each literal support in $P,Q,S$, its cell set,
`FootprintVertices`, boundary footprint, and centroid equal the
corresponding observable of the certificate's labelled support.  No
adjacency, marked-point, local-sector, or Laplacian assertion is part of
this datum.
-/
structure BandOrderedGeneralOdometerRowData
    (q : Fin 4 -> CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C0 : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C0 T)
    (h : PartialOdometer)
    (P : Fin 3 -> Bool -> ProtoTile)
    (r : Fin 3 -> Bool -> PartialOdometer)
    (Q S : Fin 3 -> Bool -> ProtoTile)
    (u v : Fin 3 -> Bool -> PartialOdometer)
    (g : IntegerLatticeFunction) : Prop where
-- BODY
  hroot : TileOdometer (q 0) T h
  hPband : BandPrototile (q 0) T
  hP : forall i s, TileOdometer (q i.succ) (P i s) (r i s)
  hPcells : forall z, z ∈ T.cells <-> exists i s, z ∈ (P i s).cells
  hPfoot : forall i s,
    FootprintVertices (P i s) ⊆ FootprintVertices T
  hPcent : forall i s,
    TileCentroid (P i s) - TileCentroid T =
      (if s = true then (1 : Real) else -1) •
        ((1 / 2 : Real) •
          (GaussianRealPoint
              (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
            (-((GaussianRealPoint
                (BandVectors.1 (q ((i + 2).succ))
                  (q ((i + 1).succ)))).2),
              (GaussianRealPoint
                (BandVectors.1 (q ((i + 2).succ))
                  (q ((i + 1).succ)))).1)))
  hPdom : forall z, z ∈ h.domain <-> exists i s, z ∈ (r i s).domain
  hPvalue : forall i s z, z ∈ (r i s).domain ->
    h.value z = (r i s).value z
  hPcompat : forall i s j t, OdometerCompatibility (r i s) (r j t)
  hPslope : forall i s, (q i.succ).1 = 0 \/
    exists p pi : Real × Real,
      PartialOdometerSlope h = some p /\
      PartialOdometerSlope (r i s) = some pi /\
      pi.1 - p.1 =
        (if s = true then (1 : Real) else -1) * (1 / 2) *
          (((BandVectors.2 (q ((i + 2).succ))
              (q ((i + 1).succ))).re : Int) -
           ((BandVectors.2 (q ((i + 2).succ))
              (q ((i + 1).succ))).im : Int)) /\
      pi.2 - p.2 =
        (if s = true then (1 : Real) else -1) * (1 / 2) *
          (((BandVectors.2 (q ((i + 2).succ))
              (q ((i + 1).succ))).im : Int) +
           ((BandVectors.2 (q ((i + 2).succ))
              (q ((i + 1).succ))).re : Int))
  hQroot : TileOdometer (cfg.firstPredecessor 0)
    (P 0 true) (r 0 true)
  hSroot : TileOdometer (cfg.firstPredecessor 0)
    (P 0 false) (r 0 false)
  hQband : BandPrototile (cfg.firstPredecessor 0) (P 0 true)
  hSband : BandPrototile (cfg.firstPredecessor 0) (P 0 false)
  hQ : forall i s,
    TileOdometer (cfg.firstPredecessor i.succ) (Q i s) (u i s)
  hS : forall i s,
    TileOdometer (cfg.firstPredecessor i.succ) (S i s) (v i s)
  hQcells : forall z, z ∈ (P 0 true).cells <->
    exists i s, z ∈ (Q i s).cells
  hScells : forall z, z ∈ (P 0 false).cells <->
    exists i s, z ∈ (S i s).cells
  hQfoot : forall i s,
    FootprintVertices (Q i s) ⊆ FootprintVertices (P 0 true)
  hSfoot : forall i s,
    FootprintVertices (S i s) ⊆ FootprintVertices (P 0 false)
  hQcent : forall i s,
    TileCentroid (Q i s) - TileCentroid (P 0 true) =
      (if s = true then (1 : Real) else -1) •
        ((1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))) -
            (-((GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).2),
              (GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).1)))
  hScent : forall i s,
    TileCentroid (S i s) - TileCentroid (P 0 false) =
      (if s = true then (1 : Real) else -1) •
        ((1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))) -
            (-((GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).2),
              (GaussianRealPoint (BandVectors.1
              (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ)))).1)))
  hQdom : forall z, z ∈ (r 0 true).domain <->
    exists i s, z ∈ (u i s).domain
  hSdom : forall z, z ∈ (r 0 false).domain <->
    exists i s, z ∈ (v i s).domain
  hQvalue : forall i s z, z ∈ (u i s).domain ->
    (r 0 true).value z = (u i s).value z
  hSvalue : forall i s z, z ∈ (v i s).domain ->
    (r 0 false).value z = (v i s).value z
  hQcompat : forall i s j t, OdometerCompatibility (u i s) (u j t)
  hScompat : forall i s j t, OdometerCompatibility (v i s) (v j t)
  hQslope : forall i s, (cfg.firstPredecessor i.succ).1 = 0 \/
    exists p pi : Real × Real,
      PartialOdometerSlope (r 0 true) = some p /\
      PartialOdometerSlope (u i s) = some pi /\
      pi.1 - p.1 =
        (if s = true then (1 : Real) else -1) * (1 / 2) *
          (((BandVectors.2 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))).re : Int) -
           ((BandVectors.2 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))).im : Int)) /\
      pi.2 - p.2 =
        (if s = true then (1 : Real) else -1) * (1 / 2) *
          (((BandVectors.2 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))).im : Int) +
           ((BandVectors.2 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))).re : Int))
  hSslope : forall i s, (cfg.firstPredecessor i.succ).1 = 0 \/
    exists p pi : Real × Real,
      PartialOdometerSlope (r 0 false) = some p /\
      PartialOdometerSlope (v i s) = some pi /\
      pi.1 - p.1 =
        (if s = true then (1 : Real) else -1) * (1 / 2) *
          (((BandVectors.2 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))).re : Int) -
           ((BandVectors.2 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))).im : Int)) /\
      pi.2 - p.2 =
        (if s = true then (1 : Real) else -1) * (1 / 2) *
          (((BandVectors.2 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))).im : Int) +
           ((BandVectors.2 (cfg.firstPredecessor ((i + 2).succ))
              (cfg.firstPredecessor ((i + 1).succ))).re : Int))
  hextP : forall i s, GlobalOdometerExtends g (r i s)
  hextQ : forall i s, GlobalOdometerExtends g (u i s)
  hextS : forall i s, GlobalOdometerExtends g (v i s)
  hcompat : forall a b : PartialOdometer,
    (exists i s, a = r i s \/ a = u i s \/ a = v i s) ->
    (exists i s, b = r i s \/ b = u i s \/ b = v i s) ->
    OdometerCompatibility a b
  hobsP : forall i s,
    (P i s).cells = (cert.P i s).cells /\
    FootprintVertices (P i s) = FootprintVertices (cert.P i s) /\
    BoundaryFootprintVertices (P i s) =
      BoundaryFootprintVertices (cert.P i s) /\
    TileCentroid (P i s) = TileCentroid (cert.P i s)
  hobsQ : forall i s,
    (Q i s).cells = (cert.Q i s).cells /\
    FootprintVertices (Q i s) = FootprintVertices (cert.Q i s) /\
    BoundaryFootprintVertices (Q i s) =
      BoundaryFootprintVertices (cert.Q i s) /\
    TileCentroid (Q i s) = TileCentroid (cert.Q i s)
  hobsS : forall i s,
    (S i s).cells = (cert.S i s).cells /\
    FootprintVertices (S i s) = FootprintVertices (cert.S i s) /\
    BoundaryFootprintVertices (S i s) =
      BoundaryFootprintVertices (cert.S i s) /\
    TileCentroid (S i s) = TileCentroid (cert.S i s)

end ApollonianSuperharmonic

end
