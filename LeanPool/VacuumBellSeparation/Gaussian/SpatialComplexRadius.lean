/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialBesselComplexIntegral
public import Mathlib.Analysis.RCLike.Sqrt

/-!
# The actual principal complex radius of separated spatial vectors

The squared radius is the bilinear coordinate sum, not the Hermitian
norm. Euclidean control of the complex displacement proves that it stays
in the right half-plane and gives the manuscript's lower real-part bound.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ComplexOrder

/-- Spatial squared radius given by `∑ j : Fin 3, ((if j = 0 then (s : ℂ) else 0) + δ j) ^ 2`. -/
noncomputable def spatialSquaredRadius (s : ℝ) (δ : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  ∑ j : Fin 3, ((if j = 0 then (s : ℂ) else 0) + δ j) ^ 2

/-- Spatial complex radius obtained from `Complex.sqrt`. -/
noncomputable def spatialComplexRadius (s : ℝ) (δ : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  Complex.sqrt (spatialSquaredRadius s δ)

theorem spatialSquaredRadius_expand (s : ℝ) (δ : EuclideanSpace ℂ (Fin 3)) :
    spatialSquaredRadius s δ = (s : ℂ) ^ 2 + 2 * (s : ℂ) * δ 0 + ∑ j, δ j ^ 2 := by
  simp only [spatialSquaredRadius, Fin.sum_univ_succ]
  norm_num; ring

theorem spatial_bilinear_square_norm_le (δ : EuclideanSpace ℂ (Fin 3)) :
    ‖∑ j : Fin 3, δ j ^ 2‖ ≤ ‖δ‖ ^ 2 := by
  calc
    _ ≤ ∑ j : Fin 3, ‖δ j ^ 2‖ := norm_sum_le _ _
    _ = ‖δ‖ ^ 2 := by simp only [norm_pow, PiLp.norm_sq_eq_of_L2]

theorem spatialSquaredRadius_error_le {s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    ‖spatialSquaredRadius s δ - (s : ℂ) ^ 2‖ ≤ 2 * s * d + d ^ 2 := by
  have hcoord : ‖δ 0‖ ≤ d := (PiLp.norm_apply_le δ 0).trans hδ
  calc
    _ = ‖2 * (s : ℂ) * δ 0 + ∑ j : Fin 3, δ j ^ 2‖ := by
      rw [spatialSquaredRadius_expand]
      congr 1
      ring
    _ ≤ ‖2 * (s : ℂ) * δ 0‖ + ‖∑ j : Fin 3, δ j ^ 2‖ := norm_add_le _ _
    _ ≤ 2 * s * d + d ^ 2 := by
      have hsq := spatial_bilinear_square_norm_le δ
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hs]
      have hm := mul_le_mul_of_nonneg_left hcoord (show 0 ≤ 2 * s by positivity)
      nlinarith [norm_nonneg δ]

theorem spatialSquaredRadius_re_lower {s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d)
    (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    s ^ 2 - 2 * s * d - d ^ 2 ≤ (spatialSquaredRadius s δ).re := by
  have h := (Complex.abs_re_le_norm (spatialSquaredRadius s δ - (s : ℂ) ^ 2)).trans
    (spatialSquaredRadius_error_le hs hd δ hδ)
  simp only [Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re] at h
  have hl := (abs_le.mp h).1
  linarith

theorem spatialSquaredRadius_re_pos {s d : ℝ} (hs : 0 < s) (hd : 0 ≤ d)
    (hsep : 4 * d ≤ s) (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    0 < (spatialSquaredRadius s δ).re := by
  have hr := spatialSquaredRadius_re_lower hs.le hd δ hδ
  have hsd := mul_le_mul_of_nonneg_right hsep hd
  have hss := mul_le_mul_of_nonneg_right hsep hs.le
  nlinarith [sq_nonneg (s - 2 * d), sq_pos_of_pos hs]

theorem spatialSquaredRadius_mem_slitPlane {s d : ℝ} (hs : 0 < s) (hd : 0 ≤ d)
    (hsep : 4 * d ≤ s) (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    spatialSquaredRadius s δ ∈ Complex.slitPlane :=
  Or.inl (spatialSquaredRadius_re_pos hs hd hsep δ hδ)

theorem spatialComplexRadius_re_lower {s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hsep : 4 * d ≤ s) (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    s - 2 * d ≤ (spatialComplexRadius s δ).re := by
  have hr := spatialSquaredRadius_re_lower hs hd δ hδ
  have hn := Complex.re_le_norm (spatialSquaredRadius s δ)
  have hsd := mul_le_mul_of_nonneg_right hsep hd
  have hb : (s - 2 * d) ^ 2 ≤
      (‖spatialSquaredRadius s δ‖ + (spatialSquaredRadius s δ).re) / 2 := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_sq (by linarith)] at hsqrt
  simpa only [spatialComplexRadius, Complex.sqrt, Complex.cpow_inv_two_re] using hsqrt

theorem spatialComplexRadius_re_half_le {s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hsep : 4 * d ≤ s) (δ : EuclideanSpace ℂ (Fin 3)) (hδ : ‖δ‖ ≤ d) :
    s / 2 ≤ (spatialComplexRadius s δ).re := by
  have h := spatialComplexRadius_re_lower hs hd hsep δ hδ
  linarith

end VacuumBellSeparation.Gaussian
