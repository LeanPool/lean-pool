/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedGradientRegularity
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-! # The weighted Laplacian and generator -/

@[expose] public section

open Bundle
open scoped ContDiff Manifold

namespace CutCur

open TauCeti.Manifold

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mgrad_eq_mgradient (f : M → ℝ) :
    mgrad F f = mgradient 𝓘(ℝ, F) f :=
  CutoffRigidity.manifoldGradient_eq_mgradient 𝓘(ℝ, F) f

theorem mlaplacian_eq_laplaceBeltrami (f : M → ℝ) :
    mlaplacian F f = laplaceBeltrami 𝓘(ℝ, F) f := by
  funext x
  rw [laplaceBeltrami_eq_sum_hessian 𝓘(ℝ, F) f x (stdOrthonormalBasis ℝ _)]
  simp only [mlaplacian, hessian_def, mgrad_eq_mgradient]

namespace WReg

/-- The Laplacian of a smooth function is smooth. -/
theorem msmooth_mlaplacian {f : M → ℝ} (hf : MSmooth F f) : MSmooth F (mlaplacian F f) := by
  rw [mlaplacian_eq_laplaceBeltrami]
  exact contMDiff_laplaceBeltrami (n := ∞) (m := ∞) (k := ∞) (by simp) (by simp) hf

/-- The weighted generator preserves smoothness. -/
theorem msmooth_mgenerator {V f : M → ℝ} (hV : MSmooth F V) (hf : MSmooth F f) :
    MSmooth F (mgenerator F V f) :=
  (msmooth_mlaplacian F hf).sub (msmooth_carre hV hf)

end WReg

end CutCur
