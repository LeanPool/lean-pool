/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: SubtileLatticeAdjacent]

/-!
# SubtileLatticeAdjacent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Let $C_i$ be a positive-curvature parent of $C_0$ in a proper quadruple.
A tile odometer $h_i$ for $C_i$ is subtile-lattice adjacent to a tile
odometer $h_0$ for $C_0$ when both slopes are defined and, for some
$s\in\{0,1,2,3\}$,
$$
 \operatorname{cent}(T(h_i))-\operatorname{cent}(T(h_0))
   =i^s\tfrac12(v_{i0}+v_{0i}),
$$
$$
 \operatorname{slope}(h_i)-\operatorname{slope}(h_0)
   =(-i)^s\tfrac12(a_{i0}+a_{0i}).
$$
The ordering of the arguments is part of the definition: subtile-lattice
adjacency is not symmetric.  Curvature-zero parents are excluded because
their singleton odometers have no slope.
-/
def SubtileLatticeAdjacent (C₀ Cᵢ : BandCircle) (T₀ Tᵢ : ProtoTile)
    (h₀ hᵢ : PartialOdometer) : Prop :=
-- BODY
  TileOdometer C₀.1.1 T₀ h₀ ∧ TileOdometer Cᵢ.1.1 Tᵢ hᵢ ∧
    ∃ p₀ pᵢ : ℝ × ℝ,
      PartialOdometerSlope h₀ = some p₀ ∧
      PartialOdometerSlope hᵢ = some pᵢ ∧
      ∃ q : Fin 4 → CircleCoordinates, ∃ i : Fin 3, ∃ s : Fin 4,
        ProperBandQuadruple q ∧ q 0 = C₀.1.1 ∧ q i.succ = Cᵢ.1.1 ∧
        TileCentroid Tᵢ - TileCentroid T₀ =
          (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨0, 1⟩ : GaussianInt) ^ s.val *
              (BandVectors.1 (q i.succ) (q 0) +
               BandVectors.1 (q 0) (q i.succ))) ∧
        pᵢ.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
          ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.2 (q i.succ) (q 0) +
             BandVectors.2 (q 0) (q i.succ)))).1 ∧
        pᵢ.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
          ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.2 (q i.succ) (q 0) +
             BandVectors.2 (q 0) (q i.succ)))).2

end ApollonianSuperharmonic

end
