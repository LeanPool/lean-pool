/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.SixSubtileLabel
public import LeanPool.ApollonianSuperharmonic.P4250T1SlopeOffset
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: P4261T1PlacedOdometer]

/-!
# P4261T1PlacedOdometer

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Fix an ordered-general layout $\mathcal L$ on $(q,T_0)$ and a partial
odometer $h_0$. A placed odometer at index $a=(X,m,n)$ consists of a
positive band circle $C$, a literal support $T$, and a literal partial
odometer $h$, together with the following certificates. Following the
interpretation in `SixSubtileLabel`, write
$(j,e)=(0,\mathrm{true}),(0,\mathrm{false}),(1,\mathrm{true}),
(1,\mathrm{false}),(2,\mathrm{true}),(2,\mathrm{false})$
when $X=A,B,C,D,E,F$, respectively. Then
$C=q_{j+1}$, $h$ is a tile odometer for $C$ on $T$, and $T$ has exactly
the cells and centroid of $\operatorname{Occ}_{\mathcal L}(a)$.
Its domain is exactly the raw footprint of that occurrence. There are
defined slopes $p_0=\operatorname{slope}(h_0)$ and
$p=\operatorname{slope}(h)$. Put
$w_j=a(q_{(j+2)+1},q_{(j+1)+1})$, where indices inside parentheses
are in $\mathbb Z/3\mathbb Z$. Then the slope equation is
$$
 p-p_0=\epsilon_e\,\frac12(w_j+i w_j)+m a_{01}+n a_{02},
 \qquad \epsilon_{\mathrm{true}}=1,\quad
 \epsilon_{\mathrm{false}}=-1.
$$
The half-vector is `P4250T1SlopeOffset`. The data retain the
literal function $h$; they do not choose a replacement odometer on the
same cells or require equality of auxiliary anchors of nonempty tiles.
-/
structure P4261T1PlacedOdometer
    {q : Fin 4 → CircleCoordinates} {cfg : BandOrderedGeneralConfiguration q}
    {C₀ : BandCircle} {T₀ : ProtoTile}
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀)
    (h₀ : PartialOdometer) (C : BandCircle) (T : ProtoTile)
    (h : PartialOdometer) (a : PeriodicSubtileIndex) where
-- BODY
  circle :
    let slot : Fin 3 × Bool := match a.label with
      | .A => (0, true)
      | .B => (0, false)
      | .C => (1, true)
      | .D => (1, false)
      | .E => (2, true)
      | .F => (2, false)
    C.1.1 = q slot.1.succ
  odometer : TileOdometer C.1.1 T h
  cells : T.cells = (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells
  centroid : TileCentroid T =
    TileCentroid (SubtileOccurrenceInterpretation cert.P cert.u cert.v a)
  domain : (h.domain : Set GaussianInt) =
    FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v a)
  /-- The defined slope of the literal outer odometer. -/
  rootSlope : Real × Real
  /-- The defined slope of the odometer placed at the retained periodic index. -/
  slope : Real × Real
  root_slope : PartialOdometerSlope h₀ = some rootSlope
  function_slope : PartialOdometerSlope h = some slope
  slope_offset :
    let slot : Fin 3 × Bool := match a.label with
      | .A => (0, true)
      | .B => (0, false)
      | .C => (1, true)
      | .D => (1, false)
      | .E => (2, true)
      | .F => (2, false)
    slope - rootSlope =
    (if slot.2 then (1 : Real) else -1) •
      P4250T1SlopeOffset
        (BandVectors.2 (q ((slot.1 + 2).succ))
          (q ((slot.1 + 1).succ))) +
    GaussianRealPoint
      ((a.first : GaussianInt) * BandVectors.2 (q 0) (q 1) +
        (a.second : GaussianInt) * BandVectors.2 (q 0) (q 2))

end ApollonianSuperharmonic

end
