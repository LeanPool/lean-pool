/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandCircle
public import LeanPool.ApollonianSuperharmonic.EuclideanCircleData

-- [TABLET NODE: BandCircleEuclideanData]

/-!
# BandCircleEuclideanData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
If $C=(c,w)$ is a positive-curvature band circle, its Euclidean circle
datum is
$$
             \operatorname{circ}(C)=(w/c,1/c).
$$
This is well-defined because $c>0$.  In particular, this construction is
never applied to either curvature-zero line used inside the Descartes
recursion.
-/
noncomputable def BandCircleEuclideanData (C : BandCircle) : EuclideanCircleData :=
-- BODY
  { center := (C.1.1.2 : Complex) / (C.1.1.1 : Real)
    radius := 1 / (C.1.1.1 : Real)
    radius_pos := one_div_pos.mpr (by exact_mod_cast C.2) }

end ApollonianSuperharmonic

end
