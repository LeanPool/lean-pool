/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: TileSubodometer]

/-!
# TileSubodometer

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A tile odometer $h'$ for $C'$ is an immediate subodometer of a tile
odometer $h$ for $C$ when both are certified tile odometers, the footprint
and domain of $h'$ lie in those of $h$, the two functions agree on the
smaller domain, and there is a proper quadruple with child $C$, parent
$C'$, and a sign for which the centroid displacement is the corresponding
six-piece displacement
$\pm\frac12(v_{kj}-iv_{kj})$.  Thus this relation records one actual
parent piece of the recursive construction, rather than arbitrary domain
containment.  If $C'$ has positive curvature, its slope difference from
$h$ is the corresponding $\pm\frac12(a_{kj}+ia_{kj})$; if $C'$ has zero
curvature, this is replaced by the explicit zero-curvature alternative and
no singleton slope is requested.
-/
def TileSubodometer (C C' : CircleCoordinates) (T T' : ProtoTile)
    (h h' : PartialOdometer) : Prop :=
-- BODY
  TileOdometer C T h ∧ TileOdometer C' T' h' ∧
    FootprintVertices T' ⊆ FootprintVertices T ∧
    h'.domain ⊆ h.domain ∧
    (∀ x, x ∈ h'.domain → h.value x = h'.value x) ∧
    ∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3,
      ProperBandQuadruple q ∧ q 0 = C ∧ q i.succ = C' ∧
      ∃ s : Bool,
        TileCentroid T' - TileCentroid T =
          (if s = true then (1 : Real) else -1) •
            ((1 / 2 : Real) •
              (GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
                (-((GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).2),
                  (GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).1))) ∧
        (C'.1 = 0 ∨ ∃ p p' : ℝ × ℝ,
          PartialOdometerSlope h = some p ∧
          PartialOdometerSlope h' = some p' ∧
          p'.1 - p.1 =
            (if s = true then (1 : ℝ) else -1) * (1 / 2) *
              (((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).re : ℤ) -
               ((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).im : ℤ)) ∧
          p'.2 - p.2 =
            (if s = true then (1 : ℝ) else -1) * (1 / 2) *
              (((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).im : ℤ) +
               ((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).re : ℤ)))

end ApollonianSuperharmonic

end
