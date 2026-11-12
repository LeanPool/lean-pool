/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: RightLatticeAdjacent]

/-!
# RightLatticeAdjacent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Two nondegenerate tile odometers $h,h'$ for the same positive-curvature
circle $C_0$ are right-lattice adjacent when both slopes are defined and,
for some parent $C_i$ in a proper quadruple with child $C_0$, one has with
matching signs
$$
 \operatorname{cent}(T(h'))-\operatorname{cent}(T(h))=\pm v_{0i},
 \qquad
 \operatorname{slope}(h')-\operatorname{slope}(h)=\pm a_{0i}.
$$
There is no special right-adjacency convention for unit circles.
-/
def RightLatticeAdjacent (C : BandCircle) (T T' : ProtoTile)
    (h h' : PartialOdometer) : Prop :=
-- BODY
  TileOdometer C.1.1 T h ∧ TileOdometer C.1.1 T' h' ∧
    ∃ p p' : ℝ × ℝ,
      PartialOdometerSlope h = some p ∧
      PartialOdometerSlope h' = some p' ∧
      ∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ e : Bool,
        ProperBandQuadruple q ∧ q 0 = C.1.1 ∧
        TileCentroid T' - TileCentroid T =
          (if e = true then (1 : ℝ) else -1) •
            GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) ∧
        p'.1 - p.1 = (if e = true then (1 : ℝ) else -1) *
          (BandVectors.2 (q 0) (q i.succ)).re ∧
        p'.2 - p.2 = (if e = true then (1 : ℝ) else -1) *
          (BandVectors.2 (q 0) (q i.succ)).im

end ApollonianSuperharmonic

end
