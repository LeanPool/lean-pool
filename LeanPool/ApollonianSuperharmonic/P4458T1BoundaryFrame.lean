/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryString
public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: P4458T1BoundaryFrame]

/-!
# P4458T1BoundaryFrame

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a positive band circle $C$, a Boolean chart $\epsilon$, a regular-family
base $B$, literal endpoint tiles $R^-,R^+$, and endpoint functions $h^-,h^+$,
a boundary frame consists of a positive outer circle $C_0$, a proper
quadruple $q$, a parent slot $i$, a tile $T_0$ and function $h_0$.
It records $q_0=C_0$, $q_{i+1}=C$, tile-odometer certificates for
$(C_0,T_0,h_0)$ and $(C,R^\pm,h^\pm)$, band-prototile certificates for
$T_0$ and $B$, and literal membership of both endpoints in
$\operatorname{RegularTileFamily}(B,\Lambda_C)$.
If $c_C=1$, it records $\operatorname{UnitOccurrenceOrientation}(q,i,\epsilon)$.
Writing $v_{ab}=v(q_a,q_b)$ and $a_{ab}=a(q_a,q_b)$, its centroid data are
$\operatorname{cent}(R^\pm)-\operatorname{cent}(T_0)=\tfrac12(v_{i+1,0}\pm v_{0,i+1})$.
It also records defined slopes $p_0,p^-,p^+$ of these three functions and
$p^\pm-p_0=\tfrac12(a_{i+1,0}\pm a_{0,i+1})$.
No boundary list or conclusion about restrictions is part of this data.
-/
structure P4458T1BoundaryFrame (C : BandCircle) (orientation : Bool)
    (base Rminus Rplus : ProtoTile) (hminus hplus : PartialOdometer) where
-- BODY
  /-- The positive outer circle whose decomposition contains the selected boundary. -/
  outer : BandCircle
  /-- The proper ordered presentation with that outer circle as child. -/
  q : Fin 4 → CircleCoordinates
  proper : ProperBandQuadruple q
  /-- The parent slot occupied by the selected boundary circle. -/
  slot : Fin 3
  child : q 0 = outer.1.1
  parent : q slot.succ = C.1.1
  /-- The literal outer prototile. -/
  tile : ProtoTile
  /-- The literal partial odometer on the outer prototile. -/
  odometer : PartialOdometer
  outer_odo : TileOdometer outer.1.1 tile odometer
  minus_odo : TileOdometer C.1.1 Rminus hminus
  plus_odo : TileOdometer C.1.1 Rplus hplus
  outer_band : BandPrototile outer.1.1 tile
  base_band : BandPrototile C.1.1 base
  minus_family : Rminus ∈ RegularTileFamily base (TilingLattice C)
  plus_family : Rplus ∈ RegularTileFamily base (TilingLattice C)
  chart : C.1.1.1 = 1 → UnitOccurrenceOrientation q slot orientation
  minus_centroid : TileCentroid Rminus - TileCentroid tile =
    (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.1 (q slot.succ) (q 0) - BandVectors.1 (q 0) (q slot.succ))
  plus_centroid : TileCentroid Rplus - TileCentroid tile =
    (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.1 (q slot.succ) (q 0) + BandVectors.1 (q 0) (q slot.succ))
  /-- The defined slope of the outer odometer. -/
  outer_slope : ℝ × ℝ
  /-- The defined slope at the initial boundary endpoint. -/
  minus_slope : ℝ × ℝ
  /-- The defined slope at the terminal boundary endpoint. -/
  plus_slope : ℝ × ℝ
  slope_outer : PartialOdometerSlope odometer = some outer_slope
  slope_minus : PartialOdometerSlope hminus = some minus_slope
  slope_plus : PartialOdometerSlope hplus = some plus_slope
  minus_difference : minus_slope - outer_slope =
    (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.2 (q slot.succ) (q 0) - BandVectors.2 (q 0) (q slot.succ))
  plus_difference : plus_slope - outer_slope =
    (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.2 (q slot.succ) (q 0) + BandVectors.2 (q 0) (q slot.succ))

end ApollonianSuperharmonic

end
