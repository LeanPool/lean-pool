/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.GaussianConvexity.GaussianCDFComparison
public import LeanPool.EhrhardGaussian.GaussianConvexity.StrictCDFIntegral
public import LeanPool.EhrhardGaussian.GaussianConvexity.TwoMomentComparison
public import LeanPool.EhrhardGaussian.GaussianConvexity.Normal
import Mathlib.Tactic.Linarith

/-!
# Gaussian comparison with two matching log moments

FMP25 Section 3's law-level comparison. Endpoint parameters and the interior
parameter may have either sign. Only the interior parameter zero is excluded
here; it is restored by the proved continuity of the normalized log MGF.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace EhrhardGaussian.GaussianConvexity

/-- Equality of normalized log moments at a nonzero parameter gives equality of the moments. -/
theorem mgf_id_eq_of_logMGFRatio_eq {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {p : ℝ} (hp0 : p ≠ 0)
    (hμ : Integrable (fun x => Real.exp (p * x)) μ)
    (hν : Integrable (fun x => Real.exp (p * x)) ν)
    (heq : logMGFRatio μ id p = logMGFRatio ν id p) : mgf id μ p = mgf id ν p := by
  simp only [logMGFRatio, hp0, ite_false] at heq
  have hlog := mul_left_cancel₀ (inv_ne_zero hp0) heq
  change Real.log (mgf id μ p) = Real.log (mgf id ν p) at hlog
  have h := congrArg Real.exp hlog
  rw [Real.exp_log (mgf_pos (X := id) hμ), Real.exp_log (mgf_pos (X := id) hν)] at h
  exact h

/-- A positive-scale Gaussian matching two finite log moments bounds every nonzero middle order. -/
theorem logMGFRatio_le_matching_gaussian {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hn : ¬ ∃ c, μ = Measure.dirac c) (m : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {p₀ p p₁ : ℝ} (hp₀ : p₀ < p) (hp₁ : p < p₁)
    (hp₀0 : p₀ ≠ 0) (hp0 : p ≠ 0) (hp₁0 : p₁ ≠ 0)
    (h₀ : Integrable (fun x => Real.exp (p₀ * x)) μ)
    (hp : Integrable (fun x => Real.exp (p * x)) μ)
    (h₁ : Integrable (fun x => Real.exp (p₁ * x)) μ)
    (heq₀ : logMGFRatio μ id p₀ = m + σ ^ 2 * p₀ / 2)
    (heq₁ : logMGFRatio μ id p₁ = m + σ ^ 2 * p₁ / 2) :
    logMGFRatio μ id p ≤ m + σ ^ 2 * p / 2 := by
  have := hμ.1
  let γ := gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩
  have : IsProbabilityMeasure γ :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩
  let f := fun t => μ.real (Iio t) - γ.real (Iio t)
  have hγ : ∀ r : ℝ, Integrable (fun x => Real.exp (r * x)) γ :=
    fun r => integrable_exp_mul_gaussianReal r
  have hM₀ : mgf id μ p₀ = mgf id γ p₀ :=
    mgf_id_eq_of_logMGFRatio_eq hp₀0 h₀ (hγ p₀)
      (heq₀.trans (logMGFRatio_gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩ p₀).symm)
  have hM₁ : mgf id μ p₁ = mgf id γ p₁ :=
    mgf_id_eq_of_logMGFRatio_eq hp₁0 h₁ (hγ p₁)
      (heq₁.trans (logMGFRatio_gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩ p₁).symm)
  have hc : Convex ℝ {t | 0 < f t} :=
    convex_positive_strictCDF_sub_gaussian_of_nonconstant hμ hn m hσ
  have hi : ∀ r : ℝ, r ≠ 0 → Integrable (fun x => Real.exp (r * x)) μ →
      Integrable (fun t => Real.exp (r * t) * f t) := by
    intro r hr hi
    simpa only [mul_comm] using integrable_strictCDF_sub_mul_exp hr hi (hγ r)
  have hI : ∀ r : ℝ, r ≠ 0 → Integrable (fun x => Real.exp (r * x)) μ →
      (∫ t, Real.exp (r * t) * f t) = (mgf id γ r - mgf id μ r) / r := by
    intro r hr hi
    simpa only [mul_comm] using integral_strictCDF_sub_mul_exp hr hi (hγ r)
  have hz₀ : ∫ t, Real.exp (p₀ * t) * f t = 0 := by
    rw [hI p₀ hp₀0 h₀, hM₀, sub_self, zero_div]
  have hz₁ : ∫ t, Real.exp (p₁ * t) * f t = 0 := by
    rw [hI p₁ hp₁0 h₁, hM₁, sub_self, zero_div]
  have hmiddle := integral_exp_mul_nonneg_of_convex_positive hp₀ hp₁ hc
    (hi p₀ hp₀0 h₀) (hi p₁ hp₁0 h₁) (hi p hp0 hp) hz₀ hz₁
  rw [hI p hp0 hp] at hmiddle
  have hfinal : logMGFRatio μ id p ≤ logMGFRatio γ id p := by
    simp only [logMGFRatio, hp0, ite_false]
    change p⁻¹ * Real.log (mgf id μ p) ≤ p⁻¹ * Real.log (mgf id γ p)
    rcases lt_or_gt_of_ne hp0 with hneg | hpos
    · have hnum : mgf id γ p - mgf id μ p ≤ 0 := by
        have h := (div_nonneg_iff).mp hmiddle
        rcases h with h | h
        · exact (hneg.not_ge h.2).elim
        · exact h.1
      exact mul_le_mul_of_nonpos_left
        (Real.log_le_log (mgf_pos (X := id) (hγ p)) (sub_nonpos.mp hnum)) (inv_nonpos.mpr hneg.le)
    · have hnum : 0 ≤ mgf id γ p - mgf id μ p := by
        have h := (div_nonneg_iff).mp hmiddle
        rcases h with h | h
        · exact h.1
        · exact (hpos.not_ge h.2).elim
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (mgf_pos (X := id) hp) (sub_nonneg.mp hnum)) (inv_nonneg.mpr hpos.le)
  exact hfinal.trans_eq (logMGFRatio_gaussianReal m ⟨σ ^ 2, sq_nonneg σ⟩ p)

end EhrhardGaussian.GaussianConvexity
