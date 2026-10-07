/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzConvolutionBound

/-!
# Uniform pointwise estimate for Schwartz convolution

An arbitrary scalar Schwartz kernel acts from vector L² to bounded
continuous vector fields with a bound determined by its L² norm.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Convolution

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Convolution of a complex scalar Schwartz kernel with a complex vector
Schwartz field is pointwise bounded by the product of their L² norms. -/
theorem regularised_schwartz_convolution_norm_le
    (κ : 𝓢(L2Vec3, ℂ)) (ψ : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3) :
    ‖SchwartzMap.convolution
        (ContinuousLinearMap.lsmul ℂ ℂ) κ ψ x‖ ≤
      ‖κ.toLp 2‖ * ‖ψ.toLp 2‖ := by
  have hL : ‖(ContinuousLinearMap.lsmul ℂ ℂ :
      ℂ →L[ℂ] ComplexVec3 →L[ℂ] ComplexVec3)‖ₑ ≤ 1 := by
    apply ContinuousLinearMap.opENorm_le_iff.mpr
    intro c
    have hc : ‖(ContinuousLinearMap.lsmul ℂ ℂ :
        ℂ →L[ℂ] ComplexVec3 →L[ℂ] ComplexVec3) c‖ₑ ≤ ‖c‖ₑ := by
      apply ContinuousLinearMap.opENorm_le_bound
      intro z
      change ‖c • z‖ₑ ≤ _
      exact enorm_smul_le
    rw [one_mul]
    exact hc
  have hConv := MeasureTheory.enorm_convolution_le
    (L := (ContinuousLinearMap.lsmul ℂ ℂ :
      ℂ →L[ℂ] ComplexVec3 →L[ℂ] ComplexVec3))
    (p := (2 : ℝ≥0∞)) (q := 2) (μ := volume)
    κ.continuous.aestronglyMeasurable
    ψ.continuous.aestronglyMeasurable x
  have hBound :
      ‖SchwartzMap.convolution
          (ContinuousLinearMap.lsmul ℂ ℂ) κ ψ x‖ₑ ≤
        eLpNorm κ (2 : ℝ≥0∞) volume *
          eLpNorm ψ (2 : ℝ≥0∞) volume := by
    rw [SchwartzMap.convolution_apply]
    calc
      _ ≤ ‖(ContinuousLinearMap.lsmul ℂ ℂ :
            ℂ →L[ℂ] ComplexVec3 →L[ℂ] ComplexVec3)‖ₑ *
          eLpNorm κ (2 : ℝ≥0∞) volume *
          eLpNorm ψ (2 : ℝ≥0∞) volume := hConv
      _ ≤ 1 * eLpNorm κ (2 : ℝ≥0∞) volume *
          eLpNorm ψ (2 : ℝ≥0∞) volume := by gcongr
      _ = _ := by simp
  have hFinite : (eLpNorm κ (2 : ℝ≥0∞) volume *
      eLpNorm ψ (2 : ℝ≥0∞) volume) ≠ ∞ :=
    (ENNReal.mul_lt_top (κ.memLp 2 volume).eLpNorm_lt_top
      (ψ.memLp 2 volume).eLpNorm_lt_top).ne
  have hReal := ENNReal.toReal_mono hFinite hBound
  simpa only [toReal_enorm, ENNReal.toReal_mul,
    SchwartzMap.norm_toLp] using hReal

end CKN.Leray

end
