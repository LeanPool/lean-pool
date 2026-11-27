/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalSandwichNormalization

/-!
# Literal Appendix A formulas for the commuting one-mode model

The actual inverse-power density sandwich has already been constructed on
its dense inverse domain. Here its trace is rewritten in the manuscript's
determinant form, with the actual two-dimensional real covariance gap
matrix. The covariance of its normalized density agrees with the Appendix
A rational formula. This is a specialization, not an assumption of the
general noncommuting Gaussian sandwich theorem.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

theorem thermalQuadratureVariance_sub {p q : ℝ} (hp : p < 1) (hq : q < 1) :
    thermalQuadratureVariance p - thermalQuadratureVariance q =
      (p - q) / ((1 - p) * (1 - q)) := by
  unfold thermalQuadratureVariance
  field_simp [ne_of_gt (sub_pos.mpr hp), ne_of_gt (sub_pos.mpr hq)]
  ring

/-- Thermal relative gap. -/
noncomputable def thermalRelativeGap (p q t : ℝ) : ℝ :=
  (thermalQuadratureVariance p - thermalQuadratureVariance q) /
    (thermalQuadratureVariance t - thermalQuadratureVariance q)

theorem thermalRelativeGap_lt_one {p q t : ℝ}
    (hp : p < 1) (hq : q < 1) (ht : t < 1) (hqt : q < t) (hpt : p < t) :
    thermalRelativeGap p q t < 1 := by
  have hH : 0 < thermalQuadratureVariance t - thermalQuadratureVariance q :=
    sub_pos.mpr ((thermalQuadratureVariance_lt_iff hq ht).mpr hqt)
  have hV := (thermalQuadratureVariance_lt_iff hp ht).mpr hpt
  unfold thermalRelativeGap
  rw [div_lt_one hH]
  linarith

theorem one_sub_thermalRelativeGap {p q t : ℝ}
    (hp : p < 1) (hq : q < 1) (ht : t < 1) (hqt : q < t) :
    1 - thermalRelativeGap p q t =
      ((t - p) * (1 - q)) / ((1 - p) * (t - q)) := by
  rw [thermalRelativeGap, thermalQuadratureVariance_sub hp hq,
    thermalQuadratureVariance_sub ht hq]
  field_simp [ne_of_gt (sub_pos.mpr hp), ne_of_gt (sub_pos.mpr hq),
    ne_of_gt (sub_pos.mpr ht), ne_of_gt (sub_pos.mpr hqt)]
  ring

/-- The actual real `2×2` relative covariance gap matrix of a single
isotropic mode in the manuscript's ordering of quadratures. -/
noncomputable def thermalRelativeGapMatrix (p q t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  thermalRelativeGap p q t • 1

theorem det_one_sub_thermalRelativeGapMatrix (p q t : ℝ) :
    (1 - thermalRelativeGapMatrix p q t).det = (1 - thermalRelativeGap p q t) ^ 2 := by
  norm_num [thermalRelativeGapMatrix, Matrix.det_fin_two, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply]; ring

theorem sqrt_det_one_sub_thermalRelativeGapMatrix {p q t : ℝ}
    (hp : p < 1) (hq : q < 1) (ht : t < 1) (hqt : q < t) (hpt : p < t) :
    Real.sqrt (1 - thermalRelativeGapMatrix p q t).det =
      1 - thermalRelativeGap p q t := by
  rw [det_one_sub_thermalRelativeGapMatrix,
    Real.sqrt_sq (sub_nonneg.mpr (thermalRelativeGap_lt_one hp hq ht hqt hpt).le)]

theorem thermal_parameter_lt_rpow {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ₁ : τ < 1) : q < q ^ τ := by
  have hqt : 0 < q ^ τ := Real.rpow_pos_of_pos hq₀ _
  have hrem : q ^ (1 - τ) < 1 := Real.rpow_lt_one hq₀.le hq₁ (sub_pos.mpr hτ₁)
  have hprod : q ^ τ * q ^ (1 - τ) = q := by
    rw [← Real.rpow_add hq₀, show τ + (1 - τ) = 1 by ring, Real.rpow_one]
  nlinarith

/-- The Appendix A determinant trace formula for the genuine commuting
one-mode sandwich. Both traces are the proved finite positive traces. -/
theorem positiveTrace_thermalSandwich_appendixA {p q τ : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hτ₀ : 0 < τ) (hτ₁ : τ < 1) (hpq : p < q ^ τ) :
    (positiveTrace (thermalSandwich p q τ)).toReal =
      (positiveTrace (thermalDensity q ^ (1 - τ))).toReal /
        Real.sqrt (1 - thermalRelativeGapMatrix p q (q ^ τ)).det := by
  have ht₀ : 0 < q ^ τ := Real.rpow_pos_of_pos hq₀ _
  have ht₁ : q ^ τ < 1 := Real.rpow_lt_one hq₀.le hq₁ hτ₀
  have hqt : q < q ^ τ := thermal_parameter_lt_rpow hq₀ hq₁ hτ₁
  have hrem : 0 < (1 - q) ^ (1 - τ) / (1 - q ^ (1 - τ)) :=
    div_pos (Real.rpow_pos_of_pos (sub_pos.mpr hq₁) _)
      (sub_pos.mpr (Real.rpow_lt_one hq₀.le hq₁ (sub_pos.mpr hτ₁)))
  rw [positiveTrace_thermalSandwich hp₀ hp₁ hq₀ hq₁ hpq,
    ENNReal.toReal_ofReal (thermalSandwich_traceValue_pos hp₁ hq₀ hq₁ hpq).le,
    positiveTrace_thermalDensity_rpow hq₀.le hq₁ (sub_pos.mpr hτ₁),
    ENNReal.toReal_ofReal hrem.le,
    sqrt_det_one_sub_thermalRelativeGapMatrix hp₁ hq₁ ht₁ hqt hpq,
    one_sub_thermalRelativeGap hp₁ hq₁ ht₁ hqt,
    Real.rpow_sub (sub_pos.mpr hq₁), Real.rpow_one,
    Real.rpow_sub hq₀, Real.rpow_one]
  field_simp [ht₀.ne', ne_of_gt (sub_pos.mpr hq₁),
    ne_of_gt (sub_pos.mpr hp₁), ne_of_gt (sub_pos.mpr hqt),
    ne_of_gt (sub_pos.mpr hpq),
    ne_of_gt (Real.rpow_pos_of_pos (sub_pos.mpr hq₁) τ)]

/-- The normalized actual sandwich is `thermalDensity (p/t)` by the
operator identity in `ThermalSandwichNormalization`. Its covariance is
the exact Appendix A one-mode rational expression. -/
theorem thermalSandwich_covariance_appendixA {p t : ℝ}
    (hp : p < 1) (ht₀ : 0 < t) (ht₁ : t < 1) (hpt : p < t) :
    thermalQuadratureVariance (p / t) =
      -thermalQuadratureVariance t +
        (thermalQuadratureVariance t ^ 2 - 1 / 4) /
          (thermalQuadratureVariance t - thermalQuadratureVariance p) := by
  rw [thermalQuadratureVariance_sub ht₁ hp]
  unfold thermalQuadratureVariance
  have hratio : 1 - p / t ≠ 0 :=
    ne_of_gt (sub_pos.mpr ((div_lt_one ht₀).mpr hpt))
  field_simp [ht₀.ne', hratio, ne_of_gt (sub_pos.mpr hp),
    ne_of_gt (sub_pos.mpr ht₁), ne_of_gt (sub_pos.mpr hpt)]
  ring

end VacuumBellSeparation.Gaussian
