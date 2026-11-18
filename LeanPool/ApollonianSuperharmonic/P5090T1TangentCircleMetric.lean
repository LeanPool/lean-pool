/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Complex.Module

-- [TABLET NODE: P5090T1TangentCircleMetric]

/-!
# P5090T1TangentCircleMetric

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5090T1TangentCircleMetric (c d : ℝ) (w v : ℂ) (hc : 0 < c) (hd : 0 < d)
    (hn : ‖(d : ℂ) * w - (c : ℂ) * v‖ ^ 2 = (c + d) ^ 2) :
    dist (w / c) (v / d) = 1 / c + 1 / d ∧
    (w + v) / ((c + d : ℝ) : ℂ) =
      ((1 / d) / (1 / c + 1 / d)) • (w / c) +
        ((1 / c) / (1 / c + 1 / d)) • (v / d) := by
-- BODY
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hd)
  have hcdC : ((c + d : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (add_pos hc hd))
  have hnorm : ‖(d : ℂ) * w - (c : ℂ) * v‖ = c + d := by
    nlinarith [norm_nonneg ((d : ℂ) * w - (c : ℂ) * v)]
  constructor
  · have heq : w / c - v / d =
        ((d : ℂ) * w - (c : ℂ) * v) / ((c : ℂ) * d) := by
      field_simp
    rw [dist_eq_norm, heq, Complex.norm_div, hnorm, Complex.norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hc, abs_of_pos hd]
    field_simp; ring
  · have hr (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
        (1 / y) / (1 / x + 1 / y) = x / (x + y) := by
      field_simp; ring
    rw [hr c d hc hd, add_comm (1 / c) (1 / d), hr d c hd hc, add_comm d c]
    simp only [Complex.real_smul, Complex.ofReal_div]
    field_simp


end ApollonianSuperharmonic

end
