/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.CurvatureOneOdometer

-- [TABLET NODE: P5352T2Sources]

/-!
# P5352T2Sources

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a diamond parameter $K$ with $k>1$, the four sources are tuples
$(V_j,F_j,C_j,P_j)$, consisting of a tile, an integer function, a centroid,
and a slope.  Source $0$ is
$(D_k,G_k,(0,k),(k/2,-k/2))$.  Sources $1$ and $2$ have tile
$\langle\{0\},0\rangle$, functions equal to the value functions of
$\operatorname{CurvatureOneOdometer}(i)$ and
$\operatorname{CurvatureOneOdometer}(0)$ respectively, centroid
$(1/2,1/2)$, and slopes $(1/2,1/2)$ and $(0,0)$ respectively.
Source $3$ is $(D_{k-1},G_{k-1},(0,k-1),((k-1)/2,-(k-1)/2))$.
Here $D_d=\operatorname{DiamondTile}(d)$ and
$G_d=\operatorname{DiamondOdometer}(d)$.
-/
noncomputable def P5352T2Sources (K : DiamondParameter) (hk : 1 < K.1)
    (j : Fin 4) : ProtoTile × IntegerLatticeFunction × (ℝ × ℝ) × (ℝ × ℝ) :=
-- BODY
  ![(DiamondTile K.1, DiamondOdometer K,
      (0, (K.1 : ℝ)), ((K.1 : ℝ) / 2, -((K.1 : ℝ) / 2))),
    (⟨{0}, 0⟩, (CurvatureOneOdometer ⟨0, 1⟩).value,
      (1 / 2, 1 / 2), (1 / 2, 1 / 2)),
    (⟨{0}, 0⟩, (CurvatureOneOdometer 0).value,
      (1 / 2, 1 / 2), (0, 0)),
    (DiamondTile (K.1 - 1), DiamondOdometer ⟨K.1 - 1, by omega⟩,
      (0, (K.1 : ℝ) - 1), (((K.1 : ℝ) - 1) / 2, -(((K.1 : ℝ) - 1) / 2)))] j

end ApollonianSuperharmonic

end
