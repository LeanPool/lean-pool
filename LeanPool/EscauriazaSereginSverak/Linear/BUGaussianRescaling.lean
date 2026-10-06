/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Geometry of the Gaussian average rescaling

The translated parabolic coordinates in `lem:bu-gaussian` remain in the
positive half-space and below time one.
-/

public section


open CKN CKN.Foundation.Parabolic Set

noncomputable section

namespace ESS

/-- The translated parabolic point used in `lem:bu-gaussian`. -/
@[expose] def buGaussianScaledPoint (x : Vec3) (scale σ : ℝ) (z : ParabolicPoint) : ParabolicPoint :=
  (x + scale • z.1, scale ^ 2 * (z.2 - σ))

/-- The normalized cylinder maps into the original positive half-space and
time interval of `lem:bu-gaussian`. -/
theorem buGaussian_rescaling_geometry
    (x : Vec3) (t γ : ℝ) (ht : 0 < t) (hγ : γ ≤ 1 / 12)
    (htγ : t < γ) :
    let scale := Real.sqrt (3 * t)
    let ρ := (x 2 - 1) / scale
    0 < scale ∧ scale < 1 ∧
      (∀ y : Vec3, vec3EuclideanNorm y < ρ →
        1 < (x + scale • y) 2) ∧
      (∀ s : ℝ, 1 / 6 < s → s < 3 →
        0 < scale ^ 2 * (s - 1 / 6) ∧ scale ^ 2 * (s - 1 / 6) < 1) := by
  dsimp
  let scale : ℝ := Real.sqrt (3 * t)
  let ρ : ℝ := (x 2 - 1) / scale
  have h3t : 0 < 3 * t := by positivity
  have hscalePos : 0 < scale := by dsimp [scale]; positivity
  have h3tlt : 3 * t < 1 / 4 := by
    calc
      3 * t < 3 * γ := mul_lt_mul_of_pos_left htγ (by norm_num)
      _ ≤ 3 * (1 / 12) := mul_le_mul_of_nonneg_left hγ (by norm_num)
      _ = 1 / 4 := by norm_num
  have hscaleLt : scale < 1 / 2 := by
    dsimp [scale]
    have hroot : Real.sqrt (1 / 4 : ℝ) = 1 / 2 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
    calc
      Real.sqrt (3 * t) < Real.sqrt (1 / 4) := Real.sqrt_lt_sqrt h3t.le h3tlt
      _ = 1 / 2 := hroot
  have hscaleSq : scale ^ 2 = 3 * t := by
    dsimp [scale]
    exact Real.sq_sqrt h3t.le
  have hscaleRho : scale * ρ = x 2 - 1 := by
    dsimp [ρ]
    field_simp
  refine ⟨hscalePos, hscaleLt.trans (by norm_num), ?_, ?_⟩
  · intro y hy
    have hycoord : -vec3EuclideanNorm y ≤ y 2 := by
      have hyabs := abs_apply_le_vec3EuclideanNorm y (2 : Fin 3)
      exact (neg_le_neg hyabs).trans (neg_abs_le _)
    have hscaled : -(scale * vec3EuclideanNorm y) ≤ scale * y 2 := by
      calc
        -(scale * vec3EuclideanNorm y) = scale * (-vec3EuclideanNorm y) := by ring
        _ ≤ scale * y 2 :=
          mul_le_mul_of_nonneg_left hycoord hscalePos.le
    have hradial := mul_lt_mul_of_pos_left hy hscalePos
    rw [hscaleRho] at hradial
    have hcomp : -(x 2 - 1) < scale * y 2 := by
      nlinarith only [hscaled, hradial]
    change 1 < x 2 + scale * y 2
    linarith only [hcomp]
  · intro s hslo hshi
    have hspos : 0 < s - 1 / 6 := by linarith only [hslo]
    have hscaleSqLt : scale ^ 2 < 1 / 4 := by rw [hscaleSq]; exact h3tlt
    have htimelt : scale ^ 2 * (s - 1 / 6) < 1 := by
      calc
        scale ^ 2 * (s - 1 / 6) < (1 / 4) * (s - 1 / 6) :=
          mul_lt_mul_of_pos_right hscaleSqLt hspos
        _ < 1 := by nlinarith only [hshi]
    exact ⟨mul_pos (sq_pos_of_pos hscalePos) hspos, htimelt⟩

/-- The squared growth bound after the Gaussian rescaling has its source form. -/
theorem buGaussian_rescaling_growth
    (A scale : ℝ) (x y : Vec3) (s σ : ℝ) (w : ParabolicPoint → Vec3)
    (hA : 0 ≤ A) (hscale : 0 ≤ scale)
    (hgrowth : vec3EuclideanNorm (w
      (buGaussianScaledPoint x scale σ (y, s))) ≤
      Real.exp (A * vec3EuclideanNorm
        (buGaussianScaledPoint x scale σ (y, s)).1 ^ 2)) :
    vec3EuclideanNorm (w (buGaussianScaledPoint x scale σ (y, s))) ≤
      Real.exp (2 * A * vec3EuclideanNorm x ^ 2 +
        2 * A * scale ^ 2 * vec3EuclideanNorm y ^ 2) := by
  dsimp [buGaussianScaledPoint] at hgrowth ⊢
  have htriangle : vec3EuclideanNorm (x + scale • y) ≤
      vec3EuclideanNorm x + scale * vec3EuclideanNorm y := by
    calc
      vec3EuclideanNorm (x + scale • y) ≤
          vec3EuclideanNorm x + vec3EuclideanNorm (scale • y) :=
        vec3EuclideanNorm_add_le x (scale • y)
      _ = vec3EuclideanNorm x + scale * vec3EuclideanNorm y := by
        rw [vec3EuclideanNorm_smul, abs_of_nonneg hscale]
  have hsumNonneg : 0 ≤ vec3EuclideanNorm x + scale * vec3EuclideanNorm y :=
    add_nonneg (vec3EuclideanNorm_nonneg _)
      (mul_nonneg hscale (vec3EuclideanNorm_nonneg _))
  have hsquare : vec3EuclideanNorm (x + scale • y) ^ 2 ≤
      (vec3EuclideanNorm x + scale * vec3EuclideanNorm y) ^ 2 :=
    (sq_le_sq₀ (vec3EuclideanNorm_nonneg _) hsumNonneg).2 htriangle
  have hsum : (vec3EuclideanNorm x + scale * vec3EuclideanNorm y) ^ 2 ≤
      2 * vec3EuclideanNorm x ^ 2 + 2 * scale ^ 2 * vec3EuclideanNorm y ^ 2 := by
    nlinarith only [sq_nonneg (vec3EuclideanNorm x - scale * vec3EuclideanNorm y)]
  have hspace := hsquare.trans hsum
  apply le_trans hgrowth
  apply Real.exp_le_exp.mpr
  calc
    A * vec3EuclideanNorm (x + scale • y) ^ 2 ≤
        A * (2 * vec3EuclideanNorm x ^ 2 + 2 * scale ^ 2 * vec3EuclideanNorm y ^ 2) :=
      mul_le_mul_of_nonneg_left hspace hA
    _ = 2 * A * vec3EuclideanNorm x ^ 2 +
        2 * A * scale ^ 2 * vec3EuclideanNorm y ^ 2 := by ring

end ESS
