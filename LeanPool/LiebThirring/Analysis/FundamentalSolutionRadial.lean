/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Analysis.FundamentalSolutionRegularization
import LeanPool.LiebThirring.Electrostatics.SphereRadial
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Radial normalization of the regularized Coulomb density

The elementary radial antiderivative in the fundamental solution's normalization argument, at
unit scale.

The radial primitive tends to one at infinity.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace LiebThirring

/-- The elementary radial antiderivative in the fundamental solution's normalization argument, at
unit scale. -/
theorem hasDerivAt_coulomb_radial_primitive (r : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 3 * (t ^ 2 + 1) ^ (-(3 / 2 : ℝ)))
      (3 * r ^ 2 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ))) r := by
  have hs : 0 < r ^ 2 + 1 := add_pos_of_nonneg_of_pos (sq_nonneg _) zero_lt_one
  have hh := ((hasDerivAt_id r).pow 3).fun_mul
    (((hasDerivAt_id r).pow 2).add_const 1 |>.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hs.ne'))
  simp only [Pi.pow_apply, id_eq] at hh
  convert hh using 1
  have hp : (r ^ 2 + 1) ^ (-(3 / 2 : ℝ)) =
      (r ^ 2 + 1) * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ)) := by
    calc
      _ = (r ^ 2 + 1) ^ (1 + -(5 / 2 : ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add hs, Real.rpow_one]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, mul_one]
  rw [hp]
  ring

/-- The radial primitive tends to one at infinity. -/
theorem tendsto_coulomb_radial_primitive :
    Tendsto (fun r : ℝ => r ^ 3 * (r ^ 2 + 1) ^ (-(3 / 2 : ℝ))) atTop (𝓝 1) := by
  have ht : Tendsto (fun r : ℝ => 1 + (r⁻¹) ^ 2) atTop (𝓝 (1 + 0 ^ 2)) :=
    tendsto_const_nhds.add (tendsto_inv_atTop_zero.pow 2)
  have ht' := ht.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl (by norm_num))
  norm_num only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, Real.one_rpow] at ht'
  apply ht'.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with r hr
  have hs : r ^ 2 + 1 = r ^ 2 * (1 + (r⁻¹) ^ 2) := by
    field_simp [hr.ne']
  rw [hs, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (r ^ 2) ^ (-(3 / 2 : ℝ)) = (r ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num
  rw [hp, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

/-- The radial Jacobian times the unit density is integrable and has integral one. -/
theorem coulomb_radial_integrable_integral :
    IntegrableOn (fun r : ℝ => 3 * r ^ 2 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ))) (Ioi 0) ∧
      (∫ r : ℝ in Ioi 0, 3 * r ^ 2 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ))) = 1 := by
  have hd := fun r (_ : r ∈ Ici (0 : ℝ)) => hasDerivAt_coulomb_radial_primitive r
  have hp : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ 3 * r ^ 2 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ)) := by
    intro r _
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (Real.rpow_nonneg (by positivity) _)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp tendsto_coulomb_radial_primitive, ?_⟩
  simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, sub_zero] using
    integral_Ioi_of_hasDerivAt_of_nonneg' hd hp tendsto_coulomb_radial_primitive

/-- The unit-scale regularization density is integrable on physical three-space. -/
theorem integrable_coulombApproximationDensity_one : Integrable (coulombApproximationDensity 1) :=
  by
  unfold coulombApproximationDensity
  norm_num only [one_pow, mul_one]
  apply (integrable_fun_norm_addHaar (volume : Measure Position)
    (f := fun r : ℝ => 3 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ)))).mpr
  simp only [Position, finrank_euclideanSpace_fin, Nat.reduceSub, smul_eq_mul]
  apply coulomb_radial_integrable_integral.1.congr_fun _ measurableSet_Ioi
  intro r _
  ring

/-- The regularization density has the exact Coulomb normalization `4π` at unit scale. -/
theorem integral_coulombApproximationDensity_one :
    (∫ x : Position, coulombApproximationDensity 1 x) = 4 * Real.pi := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (coulombApproximationDensity_nonneg 1))
    integrable_coulombApproximationDensity_one.aestronglyMeasurable]
  unfold coulombApproximationDensity
  norm_num only [one_pow, mul_one]
  rw [lintegral_norm (fun r : ℝ => ENNReal.ofReal (3 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ))))
    (by fun_prop)]
  have hr : (∫⁻ r : ℝ in Ioi 0,
      ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (3 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ)))) = 1 := by
    calc
      _ = ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (3 * r ^ 2 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ))) := by
        apply lintegral_congr
        intro r
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        ring
      _ = ENNReal.ofReal (∫ r : ℝ in Ioi 0, 3 * r ^ 2 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ))) := by
        apply (ofReal_integral_eq_lintegral_ofReal coulomb_radial_integrable_integral.1 ?_).symm
        filter_upwards with r
        exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg (by positivity)
          _)
      _ = 1 := by rw [coulomb_radial_integrable_integral.2, ENNReal.ofReal_one]
  rw [hr, mul_one, ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.pi)]

end LiebThirring

end
