/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedLaplacian

/-! # Linearity of `mgrad`, `mlaplacian`, `mgenerator` on smooth functions

Hence smooth `L²` eigenfunctions of `-𝓛` form a vector space.
-/

@[expose] public section

open Bundle MeasureTheory TauCeti.Manifold
open scoped Manifold ContDiff ENNReal

namespace CutCur

section EigenLinear

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mgrad_add' {f g : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) (x : M) :
    mgrad F (fun y => f y + g y) x = mgrad F f x + mgrad F g x := by
  change mgrad F (f + g) x = _
  simp only [mgrad_eq_mgradient, mgradient_add (hf.mdifferentiable (by simp))
    (hg.mdifferentiable (by simp)), Pi.add_apply]

theorem mlaplacian_add {f g : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) (x : M) :
    mlaplacian F (fun y => f y + g y) x = mlaplacian F f x + mlaplacian F g x := by
  simp only [mlaplacian_eq_laplaceBeltrami]
  exact laplaceBeltrami_add _ (hf.of_le (by simp)) (hg.of_le (by simp)) x

theorem mlaplacian_const_mul {f : M → ℝ} (c : ℝ) (hf : MSmooth F f) (x : M) :
    mlaplacian F (fun y => c * f y) x = c * mlaplacian F f x := by
  change mlaplacian F (c • f) x = _
  simp only [mlaplacian_eq_laplaceBeltrami]
  exact laplaceBeltrami_smul _ c (hf.of_le (by simp)) x

theorem mlaplacian_zero (x : M) : mlaplacian F (fun _ : M => (0 : ℝ)) x = 0 := by
  rw [mlaplacian_eq_laplaceBeltrami]
  exact laplaceBeltrami_const _ 0 x

theorem mgenerator_add {V f g : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) (x : M) :
    mgenerator F V (fun y => f y + g y) x = mgenerator F V f x + mgenerator F V g x := by
  unfold mgenerator
  rw [mlaplacian_add F hf hg, mgrad_add' F hf hg, inner_add_right]; ring

theorem mgenerator_const_mul {V f : M → ℝ} (c : ℝ) (hf : MSmooth F f) (x : M) :
    mgenerator F V (fun y => c * f y) x = c * mgenerator F V f x := by
  unfold mgenerator
  rw [mlaplacian_const_mul F c hf, mgrad_const_mul F c, inner_smul_right]
  ring

theorem mgenerator_zero {V : M → ℝ} (x : M) : mgenerator F V (fun _ : M => (0 : ℝ)) x = 0 := by
  unfold mgenerator
  rw [mlaplacian_zero, mgrad_const]; simp

end EigenLinear

end CutCur
