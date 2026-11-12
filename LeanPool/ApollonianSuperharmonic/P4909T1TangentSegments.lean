/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4828T1Disk
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.Complex.Module

-- [TABLET NODE: P4909T1TangentSegments]

/-!
# P4909T1TangentSegments

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4909T1TangentSegments (x y : ℂ) (r s : ℝ)
    (hxy : dist x y = r + s) :
    segment ℝ x y ⊆ Metric.closedBall x r ∪ Metric.closedBall y s ∧
    Disjoint (Metric.ball x r) (Metric.closedBall y s) := by
-- BODY
  constructor
  · intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have hnorm : ‖y - x‖ = r + s := by
      simpa [dist_eq_norm, norm_sub_rev] using hxy
    have hleftvec : AffineMap.lineMap x y t - x = t • (y - x) := by
      rw [AffineMap.lineMap_apply_module']
      module
    have hrightvec : AffineMap.lineMap x y t - y = (1 - t) • (x - y) := by
      rw [AffineMap.lineMap_apply_module']
      module
    have hleft : dist (AffineMap.lineMap x y t) x = t * (r + s) := by
      rw [dist_eq_norm, hleftvec, Complex.real_smul, Complex.norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht.1, hnorm]
    have hright : dist (AffineMap.lineMap x y t) y = (1 - t) * (r + s) := by
      rw [dist_eq_norm, hrightvec, Complex.real_smul, Complex.norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht.2), norm_sub_rev, hnorm]
    by_cases h : t * (r + s) ≤ r
    · exact Or.inl (Metric.mem_closedBall.mpr (by rw [hleft]; exact h))
    · exact Or.inr (Metric.mem_closedBall.mpr (by rw [hright]; linarith))
  · rw [Set.disjoint_left]
    intro z hz hw
    have hz' : dist x z < r := by simpa [dist_comm] using Metric.mem_ball.mp hz
    have hw' : dist z y ≤ s := Metric.mem_closedBall.mp hw
    have htri := dist_triangle x z y
    rw [hxy] at htri
    linarith

end ApollonianSuperharmonic

end
