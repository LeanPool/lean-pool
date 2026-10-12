/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Integral and L² Fourier representatives

The raw Bochner Fourier integral represents the L² Fourier transform for integrable L²
functions. Smooth compactly supported tests and tempered distributions identify the two
representatives.
-/

public section

open MeasureTheory
open scoped FourierTransform SchwartzMap TemperedDistribution ContDiff

namespace LiebThirring.Fourier

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Fourier integrals commute with Schwartz test-function pairings. -/
theorem integral_fourier_smul_eq (g : 𝓢(V, ℂ)) {f : V → H}
    (hf : Integrable f) :
    (∫ x, (𝓕 g) x • f x) = ∫ x, g x • (𝓕 f) x := by
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ V) Real.continuous_fourierChar continuous_inner g.integrable hf

/-- Inverse Fourier integrals commute with Schwartz test-function pairings. -/
theorem integral_fourierInv_smul_eq (g : 𝓢(V, ℂ)) {f : V → H}
    (hf : Integrable f) :
    (∫ x, (𝓕⁻ g) x • f x) = ∫ x, g x • (𝓕⁻ f) x := by
  simpa only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
    VectorFourier.fourierIntegral, LinearMap.neg_apply, LinearMap.flip_apply,
    innerₗ_apply_apply, neg_neg, real_inner_comm] using!
    VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -innerₗ V) (μ := (volume : Measure V)) (ν := (volume : Measure V))
    Real.continuous_fourierChar continuous_inner.neg g.integrable hf

/-- The raw Fourier integral agrees almost everywhere with the L² Fourier transform. -/
theorem fourier_toLp_ae_eq {f : V → H} (hf : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure V)) :
    ((𝓕 (hf2.toLp f) : Lp H 2 volume) : V → H) =ᵐ[volume] 𝓕 f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (hf2.toLp f))).locallyIntegrable (by norm_num))
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).locallyIntegrable
  intro g hg hc
  have hgC : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hgD : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let G : 𝓢(V, ℂ) := hgC.toSchwartzMap hgD
  have hd := congrArg (fun T : 𝓢'(V, H) => T G)
    (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  calc
    _ = ∫ x, G x • ((𝓕 (hf2.toLp f) : Lp H 2 volume) : V → H) x := by
      change (∫ x, g x • _) = ∫ x, (g x : ℂ) • _
      simp only [Complex.coe_smul]
    _ = ∫ x, (𝓕 G) x • (hf2.toLp f) x := hd.symm
    _ = ∫ x, (𝓕 G) x • f x := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, G x • (𝓕 f) x := integral_fourier_smul_eq G hf
    _ = _ := by
      change (∫ x, (g x : ℂ) • _) = ∫ x, g x • _
      simp only [Complex.coe_smul]
      rfl

/-- The raw inverse Fourier integral agrees almost everywhere with the L² inverse transform. -/
theorem fourierInv_toLp_ae_eq {f : V → H} (hf : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure V)) :
    ((𝓕⁻ (hf2.toLp f) : Lp H 2 volume) : V → H) =ᵐ[volume] 𝓕⁻ f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ (hf2.toLp f))).locallyIntegrable (by norm_num))
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      ((innerSL ℝ).continuous₂.neg) hf).locallyIntegrable
  intro g hg hc
  have hgC : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hgD : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let G : 𝓢(V, ℂ) := hgC.toSchwartzMap hgD
  have hd := congrArg (fun T : 𝓢'(V, H) => T G)
    (Lp.fourierInv_toTemperedDistribution_eq (hf2.toLp f))
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at hd
  calc
    _ = ∫ x, G x • ((𝓕⁻ (hf2.toLp f) : Lp H 2 volume) : V → H) x := by
      change (∫ x, g x • _) = ∫ x, (g x : ℂ) • _
      simp only [Complex.coe_smul]
    _ = ∫ x, (𝓕⁻ G) x • (hf2.toLp f) x := hd.symm
    _ = ∫ x, (𝓕⁻ G) x • f x := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, G x • (𝓕⁻ f) x := integral_fourierInv_smul_eq G hf
    _ = _ := by
      change (∫ x, (g x : ℂ) • _) = ∫ x, g x • _
      simp only [Complex.coe_smul]
      rfl

end LiebThirring.Fourier
end
