/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.GaussianConvexity.FMPComparison
public import LeanPool.EhrhardGaussian.GaussianConvexity.ScalarDomainBounds
public import LeanPool.EhrhardGaussian.GaussianConvexity.LogMGFBasic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Ehrhard-type laws satisfy approximate log-normal moment bounds on their finite
exponential-moment domain. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace EhrhardGaussian.GaussianConvexity

/-- Normalized Ehrhard laws satisfy the variance bound with its sharp constant two. -/
theorem variance_le_neg_two_mean {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) (hnorm : ∫ x, Real.exp x ∂μ = 1) :
    Var[id; μ] ≤ -2 * ∫ x, x ∂μ := by
  have := hμ.1
  have h0 := EhrhardType.zero_mem_interior_integrableExpSet_of_isEhrhardType hμ hexp
  have h1 : (1 : ℝ) ∈ integrableExpSet id μ := by
    change Integrable (fun x => Real.exp (1 * id x)) μ
    apply hexp.congr
    apply ae_of_all
    intro x
    change Real.exp x = Real.exp (1 * id x)
    rw [one_mul]
    rfl
  have hline := supporting_line_at_zero_on (convexOn_logMGFRatio_of_isEhrhardType hμ hexp)
    (interior_subset h0) (hasDerivAt_logMGFRatio_zero μ id h0) h1
  rw [logMGFRatio_id_zero, logMGFRatio_id_one_of_normalized μ hnorm, mul_one] at hline
  linarith only [hline]

/-- Every nonnegative negative-moment order satisfies the sharp quadratic logarithmic bound. -/
theorem log_negative_moment_le {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) {p : ℝ} (hp : 0 ≤ p) :
    Real.log (∫ x, Real.exp (-p * x) ∂μ) ≤
      -p * (∫ x, x ∂μ) + p ^ 2 / 2 * Var[id; μ] := by
  have := hμ.1
  have h0 := EhrhardType.zero_mem_interior_integrableExpSet_of_isEhrhardType hμ hexp
  have hneg : -p ∈ integrableExpSet id μ :=
    EhrhardType.integrable_exp_mul_of_isEhrhardType hμ (neg_nonpos.mpr hp)
  have hline := supporting_line_at_zero_on (convexOn_logMGFRatio_of_isEhrhardType hμ hexp)
    (interior_subset h0) (hasDerivAt_logMGFRatio_zero μ id h0) hneg
  have hmul := mul_le_mul_of_nonpos_left hline (neg_nonpos.mpr hp)
  rw [mul_logMGFRatio, logMGFRatio_id_zero] at hmul
  change Real.log (mgf id μ (-p)) ≤ _
  calc
    Real.log (mgf id μ (-p)) ≤ -p * ((∫ x, x ∂μ) + Var[id; μ] / 2 * -p) := hmul
    _ = _ := by ring

/-- A finite second positive exponential moment bounds the negative mean. -/
theorem neg_mean_le_log_second_moment {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) (hnorm : ∫ x, Real.exp x ∂μ = 1)
    (h2 : Integrable (fun x => Real.exp (2 * x)) μ) :
    -(∫ x, x ∂μ) ≤ Real.log (∫ x, Real.exp (2 * x) ∂μ) / 2 := by
  have := hμ.1
  have h0 := EhrhardType.zero_mem_interior_integrableExpSet_of_isEhrhardType hμ hexp
  have hmid := neg_zero_le_two_on_of_one_eq_zero
    (convexOn_logMGFRatio_of_isEhrhardType hμ hexp) (interior_subset h0) h2
    (logMGFRatio_id_one_of_normalized μ hnorm)
  rw [logMGFRatio_id_zero, logMGFRatio_id_two] at hmid
  exact hmid

/-- The finite second positive moment controls every negative exponential moment. -/
theorem negative_moment_le_second_moment_rpow {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) (hnorm : ∫ x, Real.exp x ∂μ = 1)
    (h2 : Integrable (fun x => Real.exp (2 * x)) μ) {p : ℝ} (hp : 0 ≤ p) :
    ∫ x, Real.exp (-p * x) ∂μ ≤
      (∫ x, Real.exp (2 * x) ∂μ) ^ (p * (p + 1) / 2) := by
  have := hμ.1
  have hv := variance_le_neg_two_mean hμ hexp hnorm
  have hm := neg_mean_le_log_second_moment hμ hexp hnorm h2
  have hlog := log_negative_moment_le hμ hexp hp
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
  have hfirst : Real.log (∫ x, Real.exp (-p * x) ∂μ) ≤
      (p + p ^ 2) * (-(∫ x, x ∂μ)) := by
    calc
      _ ≤ -p * (∫ x, x ∂μ) + p ^ 2 / 2 * Var[id; μ] := hlog
      _ ≤ -p * (∫ x, x ∂μ) + p ^ 2 / 2 * (-2 * ∫ x, x ∂μ) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hv (div_nonneg hp2 (by norm_num))) _
      _ = _ := by ring
  have hlast := hfirst.trans (mul_le_mul_of_nonneg_left hm (add_nonneg hp hp2))
  have hneg := EhrhardType.integrable_exp_mul_of_isEhrhardType hμ (neg_nonpos.mpr hp)
  have hMneg : 0 < ∫ x, Real.exp (-p * x) ∂μ := mgf_pos (X := id) hneg
  have hM2 : 0 < ∫ x, Real.exp (2 * x) ∂μ := mgf_pos (X := id) h2
  rw [Real.rpow_def_of_pos hM2]
  rw [← Real.exp_log hMneg]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (p + p ^ 2) * (Real.log (∫ x, Real.exp (2 * x) ∂μ) / 2) := hlast
    _ = _ := by ring

/-- Normalized Ehrhard-type laws satisfy the stated variance, mean and negative-moment bounds. -/
theorem ehrhardType_moment_bounds (ν : Measure ℝ) (hν : IsEhrhardType ν)
    (hexp : Integrable (fun x => Real.exp x) ν) (hnorm : ∫ x, Real.exp x ∂ν = 1) :
    Integrable (fun x => x ^ 2) ν ∧ Var[id; ν] ≤ -2 * ∫ x, x ∂ν ∧
      (∀ p : ℝ, 0 ≤ p → Real.log (∫ x, Real.exp (-p * x) ∂ν) ≤
        -p * (∫ x, x ∂ν) + p ^ 2 / 2 * Var[id; ν]) ∧
      (Integrable (fun x => Real.exp (2 * x)) ν →
        -(∫ x, x ∂ν) ≤ Real.log (∫ x, Real.exp (2 * x) ∂ν) / 2 ∧
        ∀ p : ℝ, 0 ≤ p → ∫ x, Real.exp (-p * x) ∂ν ≤
          (∫ x, Real.exp (2 * x) ∂ν) ^ (p * (p + 1) / 2)) := by
  refine ⟨EhrhardType.integrable_sq_of_isEhrhardType hν hexp,
    variance_le_neg_two_mean hν hexp hnorm, ?_, ?_⟩
  · exact fun _ hp => log_negative_moment_le hν hexp hp
  · intro h2
    exact ⟨neg_mean_le_log_second_moment hν hexp hnorm h2,
      fun _ hp => negative_moment_le_second_moment_rpow hν hexp hnorm h2 hp⟩

end EhrhardGaussian.GaussianConvexity
