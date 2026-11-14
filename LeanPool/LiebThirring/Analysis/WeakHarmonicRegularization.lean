/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import LeanPool.LiebThirring.Analysis.WeakHarmonicConvolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
/-!
# Regularization of weakly harmonic functions

Reflection about a fixed point negates the Fréchet derivative.

The Laplacian is unchanged by reflection about a fixed point.
-/
public section
open Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ContDiff
open InnerProductSpace Laplacian
namespace LiebThirring
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Reflection about a fixed point negates the Fréchet derivative. -/
lemma fderiv_reflect {b : E → F} (hb : Differentiable ℝ b) (x y : E) :
    fderiv ℝ (fun z => b (x-z)) y = - fderiv ℝ b (x-y) := by
  have hh := (hb (x-y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  calc
    _ = (fderiv ℝ b (x-y)).comp (0 - ContinuousLinearMap.id ℝ E) := hh.fderiv
    _ = _ := by
      ext v
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, zero_sub, map_neg, neg_apply]

end LiebThirring
namespace LiebThirring
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- The Laplacian is unchanged by reflection about a fixed point. -/
lemma laplacian_reflect {b : E → ℝ} (hb : ContDiff ℝ 2 b) (x y : E) :
    Δ (fun z => b (x-z)) y = Δ b (x-y) := by
  have hb₁ : Differentiable ℝ b := hb.differentiable (by norm_num)
  have hdb : ContDiff ℝ 1 (fderiv ℝ b) := hb.fderiv_right (by norm_num)
  have hd : fderiv ℝ (fun z => b (x-z)) = fun z => - fderiv ℝ b (x-z) :=
    funext (fderiv_reflect hb₁ x)
  have hdd : fderiv ℝ (fderiv ℝ (fun z => b (x-z))) y = fderiv ℝ (fderiv ℝ b) (x-y) := by
    rw [hd]
    rw [fderiv_fun_neg, fderiv_reflect (hdb.differentiable one_ne_zero), neg_neg]
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply, hdd]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [IsLocallyFiniteMeasure μ] [SFinite μ] [μ.IsAddLeftInvariant]
/-- The weak test equation makes every smooth compact-kernel convolution harmonic. -/
theorem laplacian_convolution_eq_zero_of_weak {w b : E → ℝ}
    (hw : Continuous w)
    (hweak : ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ z, w z * Δ f z ∂μ) = 0)
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (x : E) :
    Δ (w ⋆[lsmul ℝ ℝ, μ] b) x = 0 := by
  have hb₂ : ContDiff ℝ 2 b := hb.of_le (by norm_num)
  rw [laplacian_convolution hw hb₂ hbc]
  have htest := hweak (fun z => b (x-z)) (hb.comp (contDiff_const.sub contDiff_id))
    (hbc.comp_homeomorph (Homeomorph.subLeft x))
  simpa only [laplacian_reflect hb₂] using htest

end LiebThirring
end
