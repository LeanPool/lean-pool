/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Analysis.FundamentalSolutionIntegrationByParts
import LeanPool.LiebThirring.Analysis.WeakHarmonicRegularization

/-!
# Regularization of the Coulomb kernel

The regularized inverse-distance kernel of the fundamental solution.

The nonnegative approximate-identity density `-Δ G_ε` in the fundamental solution.
-/

public section

open MeasureTheory InnerProductSpace Laplacian
open scoped RealInnerProductSpace ContDiff

namespace LiebThirring

/-- The regularized inverse-distance kernel of the fundamental solution. -/
@[expose] noncomputable def regularizedCoulombKernel (ε : ℝ) (x : Position) : ℝ :=
  (‖x‖ ^ 2 + ε ^ 2) ^ (-(1 / 2 : ℝ))

/-- The nonnegative approximate-identity density `-Δ G_ε` in the fundamental solution. -/
@[expose] noncomputable def coulombApproximationDensity (ε : ℝ) (x : Position) : ℝ :=
  3 * ε ^ 2 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))

/-- The squared regularized distance is strictly positive. -/
theorem norm_sq_add_sq_pos {ε : ℝ} (hε : 0 < ε) (x : Position) :
    0 < ‖x‖ ^ 2 + ε ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)

/-- The regularized kernel is smooth everywhere for positive regularization scale. -/
theorem contDiff_regularizedCoulombKernel {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (regularizedCoulombKernel ε) :=
  ((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne
    (fun x => (norm_sq_add_sq_pos hε x).ne')

/-- First directional derivative of a regularized radial power. -/
theorem fderiv_norm_sq_add_sq_rpow {ε : ℝ} (hε : 0 < ε)
    (p : ℝ) (x v : Position) :
    fderiv ℝ (fun z : Position => (‖z‖ ^ 2 + ε ^ 2) ^ p) x v =
      2 * p * (‖x‖ ^ 2 + ε ^ 2) ^ (p - 1) * ⟪x, v⟫ := by
  have hs := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (ε ^ 2)
  have hh := hs.rpow_const (p := p) (Or.inl (norm_sq_add_sq_pos hε x).ne')
  rw [hh.fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

/-- The directional Hessian of a regularized radial power. -/
theorem hessian_norm_sq_add_sq_rpow {ε : ℝ} (hε : 0 < ε)
    (p : ℝ) (x v : Position) :
    fderiv ℝ (fderiv ℝ (fun z : Position => (‖z‖ ^ 2 + ε ^ 2) ^ p)) x v v =
      4 * p * (p - 1) * (‖x‖ ^ 2 + ε ^ 2) ^ (p - 2) * ⟪x, v⟫ ^ 2 +
        2 * p * (‖x‖ ^ 2 + ε ^ 2) ^ (p - 1) * ⟪v, v⟫ := by
  have hc : ContDiff ℝ 2 (fun z : Position => (‖z‖ ^ 2 + ε ^ 2) ^ p) :=
    ((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne
      (fun z => (norm_sq_add_sq_pos hε z).ne')
  rw [← fderiv_directional_fderiv hc]
  have hd : (fun z : Position =>
      fderiv ℝ (fun w : Position => (‖w‖ ^ 2 + ε ^ 2) ^ p) z v) =
      (fun z => 2 * p * (‖z‖ ^ 2 + ε ^ 2) ^ (p - 1) * ⟪z, v⟫) :=
    funext (fun z => fderiv_norm_sq_add_sq_rpow hε p z v)
  rw [hd]
  have hs := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (ε ^ 2)
  have hp := (hs.rpow_const (p := p - 1) (Or.inl (norm_sq_add_sq_pos hε x).ne')).const_mul (2 * p)
  have hl : HasFDerivAt (fun z : Position => ⟪z, v⟫) (innerSL ℝ v) x := by
    simpa only [coe_innerSL_apply, real_inner_comm] using (innerSL ℝ v).hasFDerivAt
  rw [(hp.fun_mul hl).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply]
  rw [show p - 1 - 1 = p - 2 by ring, real_inner_comm v x]
  ring

/-- The directional Hessian of the regularized Coulomb kernel in the fundamental solution. -/
theorem hessian_regularizedCoulombKernel {ε : ℝ} (hε : 0 < ε) (x v : Position) :
    fderiv ℝ (fderiv ℝ (regularizedCoulombKernel ε)) x v v =
      3 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) * ⟪x, v⟫ ^ 2 -
        (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) * ⟪v, v⟫ := by
  unfold regularizedCoulombKernel
  rw [hessian_norm_sq_add_sq_rpow hε]
  norm_num
  ring

/-- The exact negative Laplacian of the regularized kernel, the fundamental solution. -/
theorem laplacian_regularizedCoulombKernel {ε : ℝ} (hε : 0 < ε) (x : Position) :
    Δ (regularizedCoulombKernel ε) x = -coulombApproximationDensity ε x := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [hessian_regularizedCoulombKernel hε, real_inner_self_eq_norm_sq,
    OrthonormalBasis.norm_eq_one, one_pow, mul_one]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    (stdOrthonormalBasis ℝ Position).sum_sq_inner_left]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdim : Module.finrank ℝ Position = 3 := by
    simp only [Position, finrank_euclideanSpace_fin]
  rw [hdim]
  have hp : (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) =
      (‖x‖ ^ 2 + ε ^ 2) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) := by
    calc
      _ = (‖x‖ ^ 2 + ε ^ 2) ^ (1 + -(5 / 2 : ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add (norm_sq_add_sq_pos hε x), Real.rpow_one]
  rw [hp]
  unfold coulombApproximationDensity
  ring

/-- The density in the regularization argument is nonnegative. -/
theorem coulombApproximationDensity_nonneg (ε : ℝ) (x : Position) :
    0 ≤ coulombApproximationDensity ε x := by
  unfold coulombApproximationDensity
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (Real.rpow_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) _)

/-- Translation of the regularized Coulomb Laplacian to an arbitrary pole. -/
theorem laplacian_regularizedCoulombKernel_sub {ε : ℝ} (hε : 0 < ε)
    (y x : Position) :
    Δ (fun z => regularizedCoulombKernel ε (z - y)) x =
      -coulombApproximationDensity ε (x - y) := by
  have hc : ContDiff ℝ 2 (regularizedCoulombKernel ε) :=
    (contDiff_regularizedCoulombKernel hε).of_le (by norm_num)
  have he : (fun z => regularizedCoulombKernel ε (z - y)) =
      (fun z => regularizedCoulombKernel ε (y - z)) := by
    funext z
    simp only [regularizedCoulombKernel, norm_sub_rev]
  rw [he, laplacian_reflect hc y x, laplacian_regularizedCoulombKernel hε]
  simp only [coulombApproximationDensity, norm_sub_rev]

/-- the fundamental solution for a regularized kernel centered at an arbitrary pole. -/
theorem integral_regularizedCoulombKernel_sub_mul_laplacian {ε : ℝ} (hε : 0 < ε)
    {f : Position → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (y : Position) :
    (∫ x, regularizedCoulombKernel ε (x - y) * Δ f x) =
      -∫ x, coulombApproximationDensity ε (x - y) * f x := by
  have hc : ContDiff ℝ 2 (fun x => regularizedCoulombKernel ε (x - y)) :=
    ((contDiff_regularizedCoulombKernel hε).of_le (by norm_num)).comp
      (contDiff_id.sub contDiff_const)
  rw [integral_mul_laplacian_eq_integral_laplacian_mul hc hf hfc]
  simp_rw [laplacian_regularizedCoulombKernel_sub hε, neg_mul]
  exact integral_neg _

end LiebThirring

end
