/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedBochnerQuad
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedBochnerTest
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedLaplacian
import TauCeti.Geometry.Manifold.Riemannian.Bochner.Basic
/-!
# Weighted Bochner inequality

The drift adds the Hessian of the potential to the scalar Bochner formula.
Testing curvature-dimension against a smooth function with prescribed gradient
and zero Hessian gives the Hessian-norm term for every smooth function.
-/

@[expose] public section

open Bundle
open scoped ContDiff Manifold

namespace CutCur

open TauCeti.Manifold

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]

private theorem weighted_bochner_identity {V f : M → ℝ} (hV : MSmooth F V)
    (hf : MSmooth F f) (x : M) :
    carre2 F V f x = mHessNormSq F f x +
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).ricciTensor x
        (mgrad F f x) (mgrad F f x) +
      hessian 𝓘(ℝ, F) V x (mgrad F f x) (mgrad F f x) := by
  have hweighted := WBoch.carre2_eq F hV hf (fun φ hφ y v w => by
    simpa only [hessian_def, mgrad_eq_mgradient] using
      (hessian_symm (I := 𝓘(ℝ, F)) y
        ((hφ.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)) y) v w)) (WReg.msmooth_mlaplacian F hf) x
  rw [mlaplacian_eq_laplaceBeltrami, mlaplacian_eq_laplaceBeltrami] at hweighted
  have hcarre : carre F f f = fun y => ‖mgradient 𝓘(ℝ, F) f y‖ ^ 2 := by
    funext y
    simp only [carre, mgrad_eq_mgradient, real_inner_self_eq_norm_sq]
  rw [hcarre] at hweighted
  have hformula := laplaceBeltrami_norm_sq_mgradient hf x (stdOrthonormalBasis ℝ _)
  rw [← mHessNormSq_eq_sum_hessian F f x] at hformula
  simp only [← mgrad_eq_mgradient] at hformula hweighted
  rw [hweighted, hformula, hessian_def, ← mgrad_eq_mgradient]
  ring

/-- The Bakry–Émery curvature-dimension condition bounds the squared Hessian
and gradient by the iterated carré du champ. -/
theorem weightedBochnerIneq_of_CD {V : M → ℝ} (hV : MSmooth F V) {ρ : ℝ} (hCD : CD F ρ V) :
    WeightedBochnerIneq F V ρ := by
  intro f hf x
  obtain ⟨g, hg, hgx, hHg⟩ := WBoch.exists_test_function F x (mgrad F f x)
  have hDf := weighted_bochner_identity F hV hf x
  have hDg := weighted_bochner_identity F hV hg x
  rw [hgx, hHg] at hDg
  have hcurvature := hCD g hg x
  simp only [carre, hgx] at hcurvature ⊢
  linarith

end CutCur
