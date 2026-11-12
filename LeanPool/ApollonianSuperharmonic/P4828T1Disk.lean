/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import LeanPool.ApollonianSuperharmonic.CircleCoordinates
public import Mathlib.Analysis.Complex.Norm

-- [TABLET NODE: P4828T1Disk]

/-!
# P4828T1Disk

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a positive-curvature coordinate $C=(c,w)$ let $D(C)$ be the open
Euclidean disk with center $w/c$ and radius $1/c$. The total expression
`P4828T1Disk` uses the same formula at other curvatures; no
geometric circle interpretation is assigned to those cases.
-/
def P4828T1Disk (C : CircleCoordinates) : Set Complex :=
-- BODY
  Metric.ball ((C.2 : Complex) / (C.1 : Real)) (1 / (C.1 : Real))

end ApollonianSuperharmonic

end
