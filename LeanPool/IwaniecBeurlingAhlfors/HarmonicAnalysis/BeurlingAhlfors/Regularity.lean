/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Regularity of the Beurling–Ahlfors transform of a Schwartz function

For a Schwartz function `g`, `𝓑 g = 𝓕⁻¹ F` with `F (ξ) = m (ξ) 𝓕 g (ξ)`, `m (ξ) = (conj ξ) / ξ`.
It is
not in general a Schwartz function (`m` is discontinuous at `0`), but `|m| ≤ 1` makes `F` and
`ξ ↦ |ξ| F (ξ)` integrable, and that is all the proofs below use.

## Main results

* `HarmonicAnalysis.differentiable_beurlingPow_one`: `𝓑 g` is real-differentiable, by
  differentiation under the integral sign (Mathlib's `Real.hasFDerivAt_fourier`, through
  `𝓕⁻¹ F = 𝓕 (F (−·))`): `D (𝓑 g) (z) v = 𝓕⁻¹ (2πi ⟨ξ, v⟩ F) (z)`.
* `HarmonicAnalysis.dzbar_beurlingPow_one`: `∂_zbar (𝓑 g) = ∂g` pointwise. From the derivative,
  `∂_zbar (𝓑 g) = 𝓕⁻¹ (π i ξ m (ξ) 𝓕 g) = 𝓕⁻¹ (π i (conj ξ) 𝓕 g) = 𝓕⁻¹ (𝓕 (∂g)) = ∂g`, by Fourier
  inversion
  for the Schwartz function `∂g`.
* `HarmonicAnalysis.tendsto_beurlingPow_one_cocompact`: `𝓑 g (z) → 0` as `z → ∞`, by the
  Riemann–Lebesgue lemma for the integrable `F`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology VectorFourier
open scoped SchwartzMap FourierTransform Real ComplexConjugate RealInnerProductSpace

namespace HarmonicAnalysis

/-- `𝓑 g = 𝓕 (F (−·))` with `F = m 𝓕 g`, where `F (−·)` and `ξ ↦ |ξ| F (−ξ)` are integrable. -/
private lemma beurlingPow_one_eq_fourier (g : 𝓢(ℂ, ℂ)) :
    beurlingPow 1 (g : ℂ → ℂ) = 𝓕 (fun ξ => beurlingSymbol (-ξ) ^ 1 • 𝓕 (g : ℂ → ℂ) (-ξ)) ∧
      Integrable (fun ξ => beurlingSymbol (-ξ) ^ 1 • 𝓕 (g : ℂ → ℂ) (-ξ)) ∧
      Integrable (fun ξ : ℂ => ‖ξ‖ * ‖beurlingSymbol (-ξ) ^ 1 • 𝓕 (g : ℂ → ℂ) (-ξ)‖) := by
  set F : ℂ → ℂ := fun ξ => beurlingSymbol ξ ^ 1 • 𝓕 (g : ℂ → ℂ) ξ
  have hF : Integrable F :=
    integrable_smul_fourier (measurable_beurlingSymbol.pow_const 1)
      ⟨1, fun ξ => by simpa using norm_beurlingSymbol_le ξ⟩ g
  have hF' : Integrable (fun ξ : ℂ => ‖ξ‖ * ‖F ξ‖) := by
    have h := (𝓕 g).integrable_pow_mul volume 1
    simp only [pow_one, SchwartzMap.fourier_coe] at h
    refine h.mono (continuous_norm.aestronglyMeasurable.mul hF.1.norm)
      (ae_of_all _ fun ξ => ?_)
    simp only [norm_mul, norm_norm, F, smul_eq_mul, pow_one]
    gcongr
    calc ‖beurlingSymbol ξ‖ * ‖𝓕 (g : ℂ → ℂ) ξ‖ ≤ 1 * ‖𝓕 (g : ℂ → ℂ) ξ‖ := by
          gcongr
          exact norm_beurlingSymbol_le ξ
      _ = _ := one_mul _
  refine ⟨?_, hF.comp_neg, ?_⟩
  · rw [beurlingPow, fourierMultiplier, Real.fourierInv_eq_fourier_comp_neg]
  · simpa only [norm_neg] using hF'.comp_neg

/-- `𝓑 g` is real-differentiable for a Schwartz function `g`. -/
theorem differentiable_beurlingPow_one (g : 𝓢(ℂ, ℂ)) :
    Differentiable ℝ (beurlingPow 1 (g : ℂ → ℂ)) := by
  obtain ⟨hu, hF, hF'⟩ := beurlingPow_one_eq_fourier g
  rw [hu]
  exact Real.differentiable_fourier hF hF'

/-- `m (ξ) ξ = (conj ξ)`, also at `ξ = 0`. -/
private lemma beurlingSymbol_mul_self (ξ : ℂ) : beurlingSymbol ξ * ξ = conj ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · exact div_mul_cancel₀ _ hξ

/-- `∂_zbar (𝓑 g) = ∂g` pointwise, for a Schwartz function `g`: `D (𝓑 g) (z) v` is the inverse
Fourier transform of `2πi ⟨ξ, v⟩ F (ξ)`, so `∂_zbar (𝓑 g)` is that of
`π i ξ m (ξ) 𝓕 g (ξ) = π i (conj ξ) 𝓕 g (ξ) = 𝓕 (∂g) (ξ)`. -/
theorem dzbar_beurlingPow_one (g : 𝓢(ℂ, ℂ)) (z : ℂ) :
    dzbar (beurlingPow 1 (g : ℂ → ℂ)) z = dz (g : ℂ → ℂ) z := by
  obtain ⟨hu, hF, hF'⟩ := beurlingPow_one_eq_fourier g
  set F : ℂ → ℂ := fun ξ => beurlingSymbol (-ξ) ^ 1 • 𝓕 (g : ℂ → ℂ) (-ξ) with hFdef
  set G := fourierSMulRight (innerSL ℝ) F
  have hG : Integrable G := by
    refine (hF'.const_mul (2 * π * ‖(innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)‖)).mono'
      hF.1.fourierSMulRight (ae_of_all _ fun v => ?_)
    rw [← mul_assoc]
    exact norm_fourierSMulRight_le _ _ _
  -- the derivative in the direction `a`: `D (𝓑 g) (z) a = 𝓕 (−2πi ⟨·, a⟩ F) (z)`
  have hD : ∀ a : ℂ, fderiv ℝ (beurlingPow 1 (g : ℂ → ℂ)) z a =
      ∫ v, 𝐞 (-⟪v, z⟫) • (-(2 * π * Complex.I) • ⟪v, a⟫ • F v) := fun a => by
    rw [hu, (Real.hasFDerivAt_fourier hF hF' z).fderiv, Real.fourier_continuousLinearMap_apply hG]
    rfl
  have hint : ∀ a : ℂ, Integrable (fun v => 𝐞 (-⟪v, z⟫) • (-(2 * π * Complex.I) • ⟪v, a⟫ • F v)) :=
    fun a => (Real.fourierIntegral_convergent_iff z).2 (hG.apply_continuousLinearMap a)
  -- `∂g = 𝓕⁻¹ (𝓕 (∂g)) = 𝓕 (π i (conj ξ) 𝓕 g) (−·)`
  have hdz : dz (g : ℂ → ℂ) z =
      ∫ v, 𝐞 (-⟪v, z⟫) • (((π : ℂ) * Complex.I * conj (-v)) • 𝓕 (g : ℂ → ℂ) (-v)) := by
    have hinv : 𝓕⁻ (𝓕 (dzCLM g)) = (dzCLM g : 𝓢(ℂ, ℂ)) := FourierTransform.fourierInv_fourier_eq _
    rw [← dzCLM_apply, ← hinv, SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe,
      Real.fourierInv_eq_fourier_comp_neg, Real.fourier_eq]
    simp only [fourier_dzCLM]
  have hI : Integrable (fun v => Complex.I •
      (𝐞 (-⟪v, z⟫) • (-(2 * π * Complex.I) • ⟪v, Complex.I⟫ • F v))) :=
    (hint Complex.I).smul (Complex.I : ℂ)
  rw [dzbar, hD, hD, hdz, ← integral_smul, ← integral_add (hint 1) hI, ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  have hv : (⟪v, 1⟫ : ℂ) + Complex.I * ⟪v, Complex.I⟫ = v := by
    apply Complex.ext <;> simp [Complex.inner]
  have hm := beurlingSymbol_mul_self v
  simp only [hFdef, beurlingSymbol_neg, pow_one, Circle.smul_def, smul_eq_mul, Complex.real_smul,
    map_neg]
  linear_combination
    (-(π : ℂ) * Complex.I * (𝐞 (-⟪v, z⟫) : ℂ) * beurlingSymbol v * 𝓕 (g : ℂ → ℂ) (-v)) * hv +
    (-(π : ℂ) * Complex.I * (𝐞 (-⟪v, z⟫) : ℂ) * 𝓕 (g : ℂ → ℂ) (-v)) * hm

/-- `𝓑 g (z) → 0` as `z → ∞`, for a Schwartz function `g`: the Riemann–Lebesgue lemma. -/
theorem tendsto_beurlingPow_one_cocompact (g : 𝓢(ℂ, ℂ)) :
    Tendsto (beurlingPow 1 (g : ℂ → ℂ)) (cocompact ℂ) (𝓝 0) := by
  rw [(beurlingPow_one_eq_fourier g).1]
  exact tendsto_integral_exp_inner_smul_cocompact _

end HarmonicAnalysis
