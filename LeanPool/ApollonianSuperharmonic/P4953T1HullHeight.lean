/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.Complex.Module

-- [TABLET NODE: P4953T1HullHeight]

/-!
# P4953T1HullHeight

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4953T1HullHeight (h : ℝ) (A B x : ℂ)
    (hx : x ∈ interior (convexHull ℝ
      ({A, B, ⟨h, A.im⟩, ⟨h, B.im⟩} : Set ℂ))) :
    min A.im B.im < x.im ∧ x.im < max A.im B.im := by
-- BODY
  let u := min A.im B.im
  let v := max A.im B.im
  let strip : Set ℂ := {z | u ≤ z.im ∧ z.im ≤ v}
  have hconv : Convex ℝ strip := by
    intro z hz w hw r s hr hs hrs
    change u ≤ z.im ∧ z.im ≤ v at hz
    change u ≤ w.im ∧ w.im ≤ v at hw
    change u ≤ (r • z + s • w).im ∧ (r • z + s • w).im ≤ v
    simp only [Complex.add_im, Complex.smul_im]
    constructor
    · calc
        u = r * u + s * u := by rw [← add_mul, hrs, one_mul]
        _ ≤ r * z.im + s * w.im := add_le_add
          (mul_le_mul_of_nonneg_left hz.1 hr) (mul_le_mul_of_nonneg_left hw.1 hs)
    · calc
        r * z.im + s * w.im ≤ r * v + s * v := add_le_add
          (mul_le_mul_of_nonneg_left hz.2 hr) (mul_le_mul_of_nonneg_left hw.2 hs)
        _ = v := by rw [← add_mul, hrs, one_mul]
  have hsub : convexHull ℝ ({A, B, ⟨h, A.im⟩, ⟨h, B.im⟩} : Set ℂ) ⊆ strip := by
    apply convexHull_min _ hconv
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    all_goals first
      | exact ⟨min_le_left _ _, le_max_left _ _⟩
      | exact ⟨min_le_right _ _, le_max_right _ _⟩
  have hxint := interior_mono hsub hx
  have hxweak := interior_subset hxint
  change u ≤ x.im ∧ x.im ≤ v at hxweak
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hxint)
  have step (r : ℝ) (hr : |r| < ε) : x + (r : ℂ) * Complex.I ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left,
      Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hr
  have hlo := hball (step (-ε / 2) (by rw [abs_of_neg (by linarith)]; linarith))
  have hhi := hball (step (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith))
  change u ≤ (x + ((-ε / 2 : ℝ) : ℂ) * Complex.I).im ∧ _ at hlo
  change _ ∧ (x + ((ε / 2 : ℝ) : ℂ) * Complex.I).im ≤ v at hhi
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hlo hhi
  constructor <;> linarith [hlo.1, hhi.2]

end ApollonianSuperharmonic

end
