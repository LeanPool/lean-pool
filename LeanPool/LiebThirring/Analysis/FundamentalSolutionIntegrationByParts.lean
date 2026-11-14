/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import LeanPool.LiebThirring.Analysis.FundamentalSolutionIntegrability
import LeanPool.LiebThirring.Analysis.WeakHarmonicConvolution

/-!
# Compact-test integration by parts for the Laplacian

Evaluation of the first Fréchet derivative in a fixed direction commutes with differentiation.

Two integrations by parts in one direction, with a compactly supported test.
-/

public section

open MeasureTheory InnerProductSpace Laplacian

namespace LiebThirring

/-- Evaluation of the first Fréchet derivative in a fixed direction
commutes with differentiation. -/
theorem fderiv_directional_fderiv {f : Position → ℝ} (hf : ContDiff ℝ 2 f)
    (x u v : Position) :
    fderiv ℝ (fun z => fderiv ℝ f z v) x u =
      fderiv ℝ (fderiv ℝ f) x u v := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  rw [fderiv_clm_apply (hd.differentiable one_ne_zero x) (differentiableAt_const v)]
  rw [(hasFDerivAt_const v x).fderiv]
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

/-- Two integrations by parts in one direction, with a compactly supported test. -/
theorem integral_mul_hessian_eq_integral_hessian_mul
    {u f : Position → ℝ} (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (v : Position) :
    (∫ x, u x * fderiv ℝ (fderiv ℝ f) x v v) =
      ∫ x, fderiv ℝ (fderiv ℝ u) x v v * f x := by
  let du := fun x => fderiv ℝ u x v
  let df := fun x => fderiv ℝ f x v
  have hdu : ContDiff ℝ 1 du :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdf : ContDiff ℝ 1 df :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdfc : HasCompactSupport df :=
    (hfc.fderiv ℝ).comp_left (map_zero (ContinuousLinearMap.apply ℝ ℝ v))
  have hdf' (x : Position) : fderiv ℝ df x v = fderiv ℝ (fderiv ℝ f) x v v :=
    fderiv_directional_fderiv hf x v v
  have hdu' (x : Position) : fderiv ℝ du x v = fderiv ℝ (fderiv ℝ u) x v v :=
    fderiv_directional_fderiv hu x v v
  have hfirst : (∫ x, u x * fderiv ℝ df x v) = - ∫ x, du x * df x := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact (hdu.continuous.mul hdf.continuous).integrable_of_hasCompactSupport hdfc.mul_left
    · simp_rw [hdf']
      exact (hu.continuous.mul (continuous_kernel_hessian hf v v)).integrable_of_hasCompactSupport
        (hasCompactSupport_kernel_hessian hfc v v).mul_left
    · exact (hu.continuous.mul hdf.continuous).integrable_of_hasCompactSupport hdfc.mul_left
    · exact fun x _ => hu.differentiable (by norm_num) x
    · exact fun x _ => hdf.differentiable one_ne_zero x
  have hsecond : (∫ x, du x * fderiv ℝ f x v) = - ∫ x, fderiv ℝ du x v * f x := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · simp_rw [hdu']
      exact ((continuous_kernel_hessian hu v v).mul hf.continuous).integrable_of_hasCompactSupport
        hfc.mul_left
    · exact (hdu.continuous.mul hdf.continuous).integrable_of_hasCompactSupport hdfc.mul_left
    · exact (hdu.continuous.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left
    · exact fun x _ => hdu.differentiable one_ne_zero x
    · exact fun x _ => hf.differentiable (by norm_num) x
  simp_rw [hdf'] at hfirst
  simp_rw [hdu'] at hsecond
  exact hfirst.trans ((congrArg Neg.neg hsecond).trans (neg_neg _))

/-- The Mathlib Laplacian is self-adjoint against compactly supported `C²` tests. -/
theorem integral_mul_laplacian_eq_integral_laplacian_mul
    {u f : Position → ℝ} (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (∫ x, u x * Δ f x) = ∫ x, Δ u x * f x := by
  simp_rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum, integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => integral_mul_hessian_eq_integral_hessian_mul hu hf hfc _)
  · intro i _
    exact ((continuous_kernel_hessian hu _ _).mul hf.continuous).integrable_of_hasCompactSupport
      hfc.mul_left
  · intro i _
    exact (hu.continuous.mul (continuous_kernel_hessian hf _ _)).integrable_of_hasCompactSupport
      (hasCompactSupport_kernel_hessian hfc _ _).mul_left

end LiebThirring

end
