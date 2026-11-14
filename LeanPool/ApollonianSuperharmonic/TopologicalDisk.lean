/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Real


-- [TABLET NODE: TopologicalDisk]

/-!
# TopologicalDisk

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A plane set homeomorphic to the closed unit ball for the product norm.
This ball is a square, homeomorphic to the closed Euclidean unit disk.
-/
def TopologicalDisk (S : Set (Real × Real)) : Prop :=
-- BODY
  Nonempty
    ((Metric.closedBall (0 : Real × Real) 1 : Set (Real × Real)) ≃ₜ
      S)

end ApollonianSuperharmonic

end
