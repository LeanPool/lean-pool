/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandCircleEuclideanData
public import Mathlib.Analysis.Complex.Basic

-- [TABLET NODE: BandPackingExterior]

/-!
# BandPackingExterior

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A point $z\in\mathbb C$ is exterior to the open disks of the band packing
if, for every positive-curvature band circle $C$, one has
$$
 \operatorname{circ}(C).\operatorname{radius}
 \le |z-\operatorname{circ}(C).\operatorname{center}|.
$$
Boundary and tangency points are therefore exterior; points in an open
band disk are not.
-/
def BandPackingExterior (z : Complex) : Prop :=
-- BODY
  ∀ C : BandCircle,
    (BandCircleEuclideanData C).radius ≤
      dist z (BandCircleEuclideanData C).center

end ApollonianSuperharmonic

end
