/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.Meridional
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Setting.RotationLemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# L4 L6

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- A pointwise bound on the `(2/3)`-power of the `L^6` spatial integral over `B(0,r)`
for each time `t` in the backward parabolic cylinder, derived from the `L^6` bound over
`B(0,ρ)` and the inclusion `B(0,r) ⊆ B(0,ρ)`. -/
private lemma spatial_bound_at_time {u : ParabolicPoint → Vec3} {ρ C β r t tη : ℝ}
    (hr_le_ρ : r ≤ ρ)
    (hbound : ∀ t' ∈ Ioo tη 0,
      (∫⁻ x in vec3Ball 0 ρ, ENNReal.ofReal (vec3EuclideanNorm (u (x, t'))) ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
        ≤ ENNReal.ofReal (C * (-t') ^ (-β)))
    (ht : t ∈ Ioo (-(r ^ 2)) 0) (hrsq_le : r ^ 2 ≤ -tη) (hC : 0 ≤ C) :
    (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (2 / 3 : ℝ) ≤
      ENNReal.ofReal (C ^ 4 * (-t) ^ (-4 * β)) := by
  have h_ball_subset : vec3Ball (0 : Vec3) r ⊆ vec3Ball (0 : Vec3) ρ :=
    vec3Ball_mono hr_le_ρ
  have h_lintegral_le : (∫⁻ x in vec3Ball 0 r,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ≤
      (∫⁻ x in vec3Ball 0 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) :=
    lintegral_mono_set h_ball_subset
  have ht_in : t ∈ Ioo tη 0 := by
    rcases ht with ⟨ht_left, ht_right⟩
    exact ⟨by linarith only [ht_left, hrsq_le], ht_right⟩
  have h_bound_t := hbound t ht_in
  have h_combined : (∫⁻ x in vec3Ball 0 r,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (1 / 6 : ℝ) ≤
      ENNReal.ofReal (C * (-t) ^ (-β)) := by
    calc
      (∫⁻ x in vec3Ball 0 r,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (1 / 6 : ℝ) ≤
          (∫⁻ x in vec3Ball 0 ρ,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (1 / 6 : ℝ) :=
        ENNReal.rpow_le_rpow h_lintegral_le (by positivity : 0 ≤ (1 / 6 : ℝ))
      _ ≤ ENNReal.ofReal (C * (-t) ^ (-β)) := h_bound_t
  have h_pow4 : ((∫⁻ x in vec3Ball 0 r,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (1 / 6 : ℝ)) ^ (4 : ℝ) ≤
      (ENNReal.ofReal (C * (-t) ^ (-β))) ^ (4 : ℝ) :=
    ENNReal.rpow_le_rpow h_combined (by norm_num : 0 ≤ (4 : ℝ))
  have h_lhs_simp : ((∫⁻ x in vec3Ball 0 r,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (1 / 6 : ℝ)) ^ (4 : ℝ) =
      (∫⁻ x in vec3Ball 0 r,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (2 / 3 : ℝ) := by
    calc
      ((∫⁻ x in vec3Ball 0 r,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (1 / 6 : ℝ)) ^ (4 : ℝ) =
          (∫⁻ x in vec3Ball 0 r,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ ((1 / 6 : ℝ) * (4 : ℝ)) := by
        rw [ENNReal.rpow_mul _ (1 / 6 : ℝ) 4]
      _ = (∫⁻ x in vec3Ball 0 r,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (2 / 3 : ℝ) := by norm_num
  have h_nonneg_arg : 0 ≤ C * (-t) ^ (-β) := by
    have h_nonneg_rpow : 0 ≤ (-t) ^ (-β) :=
      Real.rpow_nonneg (by linarith only [ht.2]) (-β)
    exact mul_nonneg hC h_nonneg_rpow
  have h_rhs_simp : (ENNReal.ofReal (C * (-t) ^ (-β))) ^ (4 : ℝ) =
      ENNReal.ofReal (C ^ 4 * (-t) ^ (-4 * β)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg h_nonneg_arg (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    rw [Real.mul_rpow hC (Real.rpow_nonneg (by linarith only [ht.2]) (-β)),
      ← Real.rpow_mul (by linarith only [ht.2]) (-β) 4,
      show (-β) * 4 = -4 * β from by ring]
    norm_cast
  rw [← h_lhs_simp, ← h_rhs_simp]
  exact h_pow4

/-- The time integral of the bound `ENNReal.ofReal (C^4 * (-t)^(-4β))` over
`Ioo (-(r^2)) 0` equals `ENNReal.ofReal (C^4 * r^(2*(1-4β)) / (1-4β))`. -/
private lemma time_integral_of_bound {r C β : ℝ} (hr_pos : 0 < r)
    (hβ_right : 4 * β < 1) (hC : 0 ≤ C) :
    ∫⁻ t in Ioo (-(r ^ 2)) 0, ENNReal.ofReal (C ^ 4 * (-t) ^ (-4 * β)) =
      ENNReal.ofReal (C ^ 4 * r ^ (2 * (1 - 4 * β)) / (1 - 4 * β)) := by
  have h_one_minus_4β_pos : 0 < 1 - 4 * β := by linarith only [hβ_right]
  have h_neg4β_gt_neg_one : -1 < -4 * β := by linarith only [hβ_right]
  have h_nonneg_C4 : 0 ≤ C ^ 4 := pow_nonneg hC 4
  set f : ℝ → ℝ := fun t => C ^ 4 * (-t) ^ (-4 * β) with hf_def
  have hf_nonneg_on : 0 ≤ᵐ[volume.restrict (Ioo (-(r ^ 2)) 0)] f := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioo (a := -(r ^ 2)) (b := 0))] with t ht
    rw [hf_def]
    have hpos : 0 ≤ (-t) ^ (-4 * β) :=
      Real.rpow_nonneg (by linarith only [ht.2]) (-4 * β)
    positivity
  have h_int_f : IntegrableOn f (Ioo (-(r ^ 2)) 0) volume := by
    have h_int_tpow : IntervalIntegrable (fun x : ℝ => x ^ (-4 * β)) volume (0 : ℝ) (r ^ 2) :=
      intervalIntegral.intervalIntegrable_rpow' h_neg4β_gt_neg_one
    have h_int_neg_tpow : IntervalIntegrable (fun x : ℝ => (-x) ^ (-4 * β))
        volume (-(r ^ 2)) (0 : ℝ) := by
      have h := (IntervalIntegrable.iff_comp_neg
        (f := fun x : ℝ => x ^ (-4 * β))).mp h_int_tpow
      simpa using h.symm
    have h_int_f' : IntervalIntegrable f volume (-(r ^ 2)) (0 : ℝ) := by
      simp only [hf_def]
      exact h_int_neg_tpow.const_mul (C ^ 4)
    -- Now convert to IntegrableOn
    have h_le : -(r ^ 2) ≤ (0 : ℝ) := neg_nonpos.mpr (sq_nonneg r)
    have h_ioc : IntegrableOn f (Ioc (-(r ^ 2)) 0) volume := by
      have h' := intervalIntegrable_iff.mp h_int_f'
      rwa [uIoc_of_le h_le] at h'
    -- Ioo (-(r^2)) 0 ⊆ Ioc (-(r^2)) 0
    exact h_ioc.mono_set Ioo_subset_Ioc_self
  have h_eq : ENNReal.ofReal (∫ t in Ioo (-(r ^ 2)) 0, f t) =
      ∫⁻ t in Ioo (-(r ^ 2)) 0, ENNReal.ofReal (f t) :=
    ofReal_integral_eq_lintegral_ofReal h_int_f hf_nonneg_on
  simp only [hf_def] at h_eq
  rw [← h_eq]
  -- Now compute the real integral
  have h_int_val : (∫ t in Ioo (-(r ^ 2)) 0, C ^ 4 * (-t) ^ (-4 * β)) =
      C ^ 4 * r ^ (2 * (1 - 4 * β)) / (1 - 4 * β) := by
    have h_le : -(r ^ 2) ≤ (0 : ℝ) := neg_nonpos.mpr (sq_nonneg r)
    calc
      (∫ t in Ioo (-(r ^ 2)) 0, C ^ 4 * (-t) ^ (-4 * β)) =
          (∫ t in (-(r ^ 2))..(0 : ℝ), C ^ 4 * (-t) ^ (-4 * β)) := by
        rw [intervalIntegral.integral_of_le h_le, integral_Ioc_eq_integral_Ioo]
      _ = C ^ 4 * (∫ t in (-(r ^ 2))..(0 : ℝ), (-t) ^ (-4 * β)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = C ^ 4 * (∫ t in (0 : ℝ)..(r ^ 2), t ^ (-4 * β)) := by
        rw [intervalIntegral.integral_comp_neg (f := fun x => x ^ (-4 * β))]
        simp
      _ = C ^ 4 * (((r ^ 2) ^ ((-4 * β) + 1) - (0 : ℝ) ^ ((-4 * β) + 1)) / ((-4 * β) + 1)) := by
        rw [integral_rpow (Or.inl h_neg4β_gt_neg_one)]
      _ = C ^ 4 * ((r ^ 2) ^ (1 - 4 * β) / (1 - 4 * β)) := by
        have : (-4 * β) + 1 = 1 - 4 * β := by ring
        rw [this]
        have h_zero_pow : (0 : ℝ) ^ (1 - 4 * β) = 0 :=
          Real.zero_rpow h_one_minus_4β_pos.ne'
        rw [h_zero_pow, sub_zero]
      _ = C ^ 4 * (r ^ (2 * (1 - 4 * β)) / (1 - 4 * β)) := by
        have h_r_sq_pow : (r ^ 2) ^ (1 - 4 * β) = r ^ (2 * (1 - 4 * β)) := by
          calc
            (r ^ 2) ^ (1 - 4 * β) = (r ^ (2 : ℝ)) ^ (1 - 4 * β) := by norm_num
            _ = r ^ ((2 : ℝ) * (1 - 4 * β)) := by
              rw [Real.rpow_mul (by linarith only [hr_pos]) (2 : ℝ) (1 - 4 * β)]
            _ = r ^ (2 * (1 - 4 * β)) := by ring
        rw [h_r_sq_pow]
      _ = C ^ 4 * r ^ (2 * (1 - 4 * β)) / (1 - 4 * β) := by ring
  rw [h_int_val]

theorem lintegral_l4l6_le_of_l6_bound {u : ParabolicPoint → Vec3} {ρ C β : ℝ} (hC : 0 ≤ C)
    (hβ : 0 ≤ β ∧ 4 * β < 1) {tη : ℝ}
    (hbound : ∀ t ∈ Ioo tη 0,
      (∫⁻ x in vec3Ball 0 ρ, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
        ≤ ENNReal.ofReal (C * (-t) ^ (-β))) :
    ∀ r : ℝ, 0 < r → r ≤ ρ → r ^ 2 ≤ -tη →
      ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (2 / 3
          : ℝ)
        ≤ ENNReal.ofReal (C ^ 4 * r ^ (2 * (1 - 4 * β)) / (1 - 4 * β)) := by
  rcases hβ with ⟨hβ_left, hβ_right⟩
  intro r hr_pos hr_le_ρ hrsq_le
  have h_meas : MeasurableSet (Ioo (-(r ^ 2)) (0 : ℝ)) := measurableSet_Ioo
  have h_pointwise : ∀ t ∈ Ioo (-(r ^ 2)) 0,
      (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (2 / 3 :
        ℝ) ≤
      ENNReal.ofReal (C ^ 4 * (-t) ^ (-4 * β)) := by
    intro t ht
    exact spatial_bound_at_time hr_le_ρ hbound ht hrsq_le hC
  have h_int_bound := time_integral_of_bound hr_pos hβ_right hC
  calc
    ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (2 / 3
          : ℝ) ≤
        ∫⁻ t in Ioo (-(r ^ 2)) 0, ENNReal.ofReal (C ^ 4 * (-t) ^ (-4 * β)) :=
      setLIntegral_mono' h_meas h_pointwise
    _ = ENNReal.ofReal (C ^ 4 * r ^ (2 * (1 - 4 * β)) / (1 - 4 * β)) := h_int_bound

end CIV
