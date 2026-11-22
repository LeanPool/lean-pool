/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedLaplacian
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedPointwise
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedVolume
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem

/-! # Weighted integration by parts from Green’s identity -/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace CutCur

open TauCeti TauCeti.Manifold

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

omit [IsContinuousRiemannianBundle F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- Integration by parts using Green's identity on a σ-compact weighted manifold. -/
theorem weightedIBP_of_isWeightedVolume_of_sigmaCompact [SigmaCompactSpace M]
    {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} (hμ : IsWeightedVolume F μ V) :
    WeightedIBP F μ V := by
  intro u v hu hv hK
  let : IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := 𝓘(ℝ, F)) (n := ∞) (V := fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)
  let ν := riemannianVolume 𝓘(ℝ, F) M
  let w : M → ℝ := fun x ↦ Real.exp (-V x)
  have hw : MSmooth F w := Real.contDiff_exp.contMDiff.comp hV.neg
  have hwmeas : Measurable (fun x ↦ ENNReal.ofReal (w x)) :=
    ENNReal.continuous_ofReal.comp hw.continuous |>.measurable
  have hwtop : ∀ᵐ x ∂ν, ENNReal.ofReal (w x) < (⊤ : ℝ≥0∞) :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hv₂ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) 2 v := hv.of_le (by simp)
  have huw₁ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) 1 (u * w) := (hu.mul hw).of_le (by simp)
  have hG := integral_mul_laplaceBeltrami huw₁ (hK.mul_right (f' := w)) hv₂
  simp only [← mlaplacian_eq_laplaceBeltrami F, ← mgrad_eq_mgradient F] at hG
  change (∫ x, (u * w) x * mlaplacian F v x ∂ν) =
    -(∫ x, carre F (u * w) v x ∂ν) at hG
  have hpair (f : M → ℝ) (x : M) : carre F f v x =
      mvfderiv 𝓘(ℝ, F) f x (mgrad F v x) := by
    calc
      _ = carre F v f x := by unfold carre; exact real_inner_comm _ _
      _ = _ := carre_eq_mvfderiv F v f x
  have hweight (x : M) : carre F w v x = -w x * carre F V v x := by
    rw [hpair w x, hpair V x]
    change mvfderiv 𝓘(ℝ, F) (Real.exp ∘ fun y ↦ -V y) x (mgrad F v x) = _
    rw [mvfderiv_comp_apply x Real.differentiableAt_exp.mdifferentiableAt
      ((hV.neg x).mdifferentiableAt (by simp)), mvfderiv_eq_fderiv,
      (Real.hasDerivAt_exp (-V x)).hasFDerivAt.fderiv]
    change mvfderiv 𝓘(ℝ, F) (fun y ↦ -V y) x (mgrad F v x) * Real.exp (-V x) = _
    rw [mvfderiv_fun_neg, neg_apply]
    dsimp only [w]
    ring
  have hproduct (x : M) : carre F (u * w) v x =
      w x * carre F u v x - w x * (u x * carre F V v x) := by
    rw [carre_mul_left F hu hw, hweight]
    ring
  simp_rw [hproduct] at hG
  have hca := WReg.msmooth_carre hu hv
  have hcv := WReg.msmooth_carre hV hv
  have ha : Integrable (fun x ↦ w x * carre F u v x) ν :=
    (hw.continuous.mul hca.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun x hx ↦ by
        change w x * carre F u v x = 0
        rw [carre, mgrad_eq_zero_of_notMem_tsupport F hx, inner_zero_left, mul_zero])
  have hb : Integrable (fun x ↦ w x * (u x * carre F V v x)) ν :=
    (hw.continuous.mul (hu.continuous.mul hcv.continuous)).integrable_of_hasCompactSupport
      hK.mul_right.mul_left
  have hc : Integrable (fun x ↦ w x * (u x * mlaplacian F v x)) ν := by
    rw [mlaplacian_eq_laplaceBeltrami]
    exact (hw.continuous.mul (hu.continuous.mul (continuous_laplaceBeltrami hv₂))
      ).integrable_of_hasCompactSupport hK.mul_right.mul_left
  rw [integral_sub ha hb] at hG
  have hmeasure : μ = ν.withDensity (fun x ↦ ENNReal.ofReal (w x)) :=
    eq_riemannianVolume_withDensity F hμ
  rw [hmeasure]
  simp only [integral_withDensity_eq_integral_toReal_smul hwmeas hwtop,
    w, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
  have hgenerator : (fun x ↦ w x * (u x * mgenerator F V v x)) =
      fun x ↦ w x * (u x * mlaplacian F v x) - w x * (u x * carre F V v x) := by
    funext x
    unfold mgenerator carre
    ring
  change (∫ x, w x * carre F u v x ∂ν) =
    -(∫ x, w x * (u x * mgenerator F V v x) ∂ν)
  rw [hgenerator, integral_sub hc hb]
  rw [show (fun x ↦ (u * w) x * mlaplacian F v x) =
      (fun x ↦ w x * (u x * mlaplacian F v x)) from funext fun x ↦ by
    simp only [Pi.mul_apply]
    ring] at hG
  linarith

end CutCur
