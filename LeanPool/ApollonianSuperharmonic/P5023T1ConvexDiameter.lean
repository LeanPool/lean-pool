/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Convex

-- [TABLET NODE: P5023T1ConvexDiameter]

/-!
# P5023T1ConvexDiameter

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5023T1ConvexDiameter (v : Fin 3 → ℂ) (s : Set ℂ) (D : ℝ)
    (hD : 0 ≤ D) (hs : s ⊆ convexHull ℝ (Set.range v))
    (hv : ∀ i j : Fin 3, dist (v i) (v j) ≤ D) :
    Metric.diam s ≤ D := by
-- BODY
  have hbounded : Bornology.IsBounded (convexHull ℝ (Set.range v)) :=
    (isBounded_convexHull (s := Set.range v)).mpr (Set.finite_range v).isBounded
  have hbase : Metric.diam (Set.range v) ≤ D := by
    apply Metric.diam_le_of_forall_dist_le hD
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact hv i j
  calc
    Metric.diam s ≤ Metric.diam (convexHull ℝ (Set.range v)) :=
      Metric.diam_mono hs hbounded
    _ = Metric.diam (Set.range v) := convexHull_diam _
    _ ≤ D := hbase

end ApollonianSuperharmonic

end
