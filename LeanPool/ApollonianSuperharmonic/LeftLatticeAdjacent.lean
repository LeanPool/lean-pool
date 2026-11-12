/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CircleMatrix
public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.UnitTriangularStep

-- [TABLET NODE: LeftLatticeAdjacent]

/-!
# LeftLatticeAdjacent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Two nondegenerate tile odometers $h,h'$ for the same positive-curvature
circle $C_0$ are left-lattice adjacent when both slopes are defined and,
for some parent $C_i$ in a proper quadruple with child $C_0$, one has with
matching signs
$$
 \operatorname{cent}(T(h'))-\operatorname{cent}(T(h))=\pm v_{i0},
 \qquad
 \operatorname{slope}(h')-\operatorname{slope}(h)=\pm a_{i0}.
$$
For a unit circle $C=(1,1+2z)$ there is the additional base convention:
there is an orientation $\epsilon$ for which the centroid step satisfies
$\operatorname{UnitStep}_{\epsilon}(v)$ in
`UnitTriangularStep`, and the slope step is $A_Cv$, where $A_C$
is `CircleMatrix`.  Thus left adjacency admits the union of the
two oriented six-step sets existentially, while each individual tile
string remains in one selected six-step graph.  This convention is part
of left adjacency only.
-/
def LeftLatticeAdjacent (C : BandCircle) (T T' : ProtoTile)
    (h h' : PartialOdometer) : Prop :=
-- BODY
  TileOdometer C.1.1 T h ∧ TileOdometer C.1.1 T' h' ∧
    ∃ p p' : ℝ × ℝ,
      PartialOdometerSlope h = some p ∧
      PartialOdometerSlope h' = some p' ∧
      ((C.1.1.1 = 1 ∧
          ∃ orientation : Bool, ∃ v : GaussianInt,
            UnitTriangularStep orientation v ∧
            TileCentroid T' - TileCentroid T = GaussianRealPoint v ∧
            p'.1 - p.1 =
              CircleMatrix C 0 0 * v.re + CircleMatrix C 0 1 * v.im ∧
            p'.2 - p.2 =
              CircleMatrix C 1 0 * v.re + CircleMatrix C 1 1 * v.im) ∨
       ∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ e : Bool,
          ProperBandQuadruple q ∧ q 0 = C.1.1 ∧
          TileCentroid T' - TileCentroid T =
            (if e = true then (1 : ℝ) else -1) •
              GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) ∧
          p'.1 - p.1 = (if e = true then (1 : ℝ) else -1) *
            (BandVectors.2 (q i.succ) (q 0)).re ∧
          p'.2 - p.2 = (if e = true then (1 : ℝ) else -1) *
            (BandVectors.2 (q i.succ) (q 0)).im)

end ApollonianSuperharmonic

end
