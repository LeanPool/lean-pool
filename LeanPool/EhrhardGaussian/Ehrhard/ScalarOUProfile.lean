/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianSmoothing
public import LeanPool.EhrhardGaussian.Ehrhard.GaussianCDF

/-! # The direct scalar OU gradient estimate in Gaussian-profile coordinates -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace EhrhardGaussian.Ehrhard

/-- The scalar Ornstein–Uhlenbeck average integrates a function against its contracted center and
Gaussian noise. -/
def scalarOU (f : ℝ → ℝ) (σ x t : ℝ) : ℝ :=
  ∫ z, f (Real.exp (-t) * x + σ * Real.sqrt (1 - Real.exp (-2 * t)) * z) ∂gaussianReal 0 1

/-- Scalar Ornstein–Uhlenbeck averaging preserves a closed interval bound. -/
theorem scalarOU_mem_Icc {f : ℝ → ℝ} (hf : Measurable f) {a b : ℝ}
    (hbound : ∀ z, f z ∈ Icc a b) (σ x t : ℝ) : scalarOU f σ x t ∈ Icc a b := by
  have hint : Integrable (fun z => f (Real.exp (-t) * x + σ * Real.sqrt (1 - Real.exp (-2 * t)) *
    z))
      (gaussianReal 0 1) := Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable
    (max |a| |b|) (ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs] using abs_le_max_abs_abs (hbound _).1 (hbound _).2)
  have hlo := integral_mono (integrable_const a) hint (fun z => (hbound _).1)
  have hhi := integral_mono hint (integrable_const b) (fun z => (hbound _).2)
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- The standard Gaussian mass above minus an argument equals its distribution function at that
argument. -/
theorem gaussian_tail_neg_eq_CDF (x : ℝ) : ((gaussianReal 0 1) (Ioi (-x))).toReal = gaussianCDF x :=
  by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hmap : (gaussianReal 0 1).map (fun z : ℝ => -z) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have hreflection : (gaussianReal 0 1) (Ioi (-x)) = (gaussianReal 0 1) (Iio x) := by
    calc
      _ = ((gaussianReal 0 1).map (fun z : ℝ => -z)) (Ioi (-x)) := by rw [hmap]
      _ = (gaussianReal 0 1) ((fun z : ℝ => -z) ⁻¹' Ioi (-x)) :=
        Measure.map_apply measurable_neg measurableSet_Ioi
      _ = _ := by congr 1; ext z; simp
  rw [hreflection, measure_congr Iio_ae_eq_Iic, gaussianCDF, cdf_eq_real]
  rfl

/-- The standard Gaussian density is even. -/
theorem gaussianPDFReal_neg (x : ℝ) : gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  simp [gaussianPDFReal_zero_one]

/-- The Gaussian distribution function inverts its quantile on the open unit interval. -/
theorem gaussianCDF_chart_symm {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    gaussianCDF (gaussianCDFChart.symm p) = p :=
  gaussianCDFChart.right_inv (gaussianCDFChart_target.symm ▸ hp)

/-- The scalar Ornstein–Uhlenbeck spatial derivative is given by its Gaussian first moment formula
at positive time and scale. -/
theorem hasDerivAt_scalarOU {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun y => scalarOU f σ y t)
      ((Real.exp (-t) / (σ * Real.sqrt (1 - Real.exp (-2 * t)))) *
        ∫ z, z * f (Real.exp (-t) * x + σ * Real.sqrt (1 - Real.exp (-2 * t)) * z)
          ∂gaussianReal 0 1) x := by
  have ha : 0 < σ * Real.sqrt (1 - Real.exp (-2 * t)) :=
    mul_pos hσ (Real.sqrt_pos.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [ht]))))
  exact hasDerivAt_gaussian_smoothing hf hbound ha.ne' (Real.exp (-t)) x

/-- The half-line extremizer estimate expressed at the inverse CDF of the
smoothed mean. No smoothness of the input is required. -/
theorem abs_deriv_scalarOU_le_profile {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (x : ℝ)
    (hmean : scalarOU f σ x t ∈ Ioo (0 : ℝ) 1) :
    |deriv (fun y => scalarOU f σ y t) x| ≤
      gaussianPDFReal 0 1 (gaussianCDFChart.symm (scalarOU f σ x t)) /
        (σ * Real.sqrt (Real.exp (2 * t) - 1)) := by
  have htail : scalarOU f σ x t = ((gaussianReal 0 1)
      (Ioi (-gaussianCDFChart.symm (scalarOU f σ x t)))).toReal := by
    rw [gaussian_tail_neg_eq_CDF, gaussianCDF_chart_symm hmean]
  have h := abs_deriv_ou_smoothing_le hf hbound hσ ht x _ htail
  simpa only [scalarOU, gaussianPDFReal_neg] using h

/-- The squared form used in the diagonal quadratic estimate. -/
theorem sq_deriv_scalarOU_le_profile {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) 1) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (x : ℝ)
    (hmean : scalarOU f σ x t ∈ Ioo (0 : ℝ) 1) :
    σ ^ 2 * (deriv (fun y => scalarOU f σ y t) x) ^ 2 ≤
      (gaussianPDFReal 0 1 (gaussianCDFChart.symm (scalarOU f σ x t))) ^ 2 /
        (Real.exp (2 * t) - 1) := by
  have hK : 0 < Real.exp (2 * t) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith only
    [ht]))
  have hden : 0 < σ * Real.sqrt (Real.exp (2 * t) - 1) := mul_pos hσ (Real.sqrt_pos.mpr hK)
  have h := (le_div_iff₀ hden).mp (abs_deriv_scalarOU_le_profile hf hbound hσ ht x hmean)
  have hsq := (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hden.le) (gaussianPDFReal_nonneg 0 1 _)).mpr h
  simp only [mul_pow, sq_abs, Real.sq_sqrt hK.le] at hsq
  apply (le_div_iff₀ hK).mpr
  nlinarith only [hsq]

end EhrhardGaussian.Ehrhard

end
