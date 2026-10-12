/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.RuminConstant
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact scalar Rumin integration

Rescaling the finite cutoff interval to `[0,1]` evaluates the squared positive part with
coefficient `9/35`. Integrability is established before conversion to the extended integral. See
Frank, Hundertmark, Jex and Nam (2018), equation (8).
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace LiebThirring.Assembly

private lemma normalized_tail (E : ℝ) (hE : 1 ≤ E) :
    (max (1 - E ^ ((3 : ℝ) / 4)) 0) ^ 2 = 0 := by
  have hp : 1 ≤ E ^ ((3 : ℝ) / 4) := Real.one_le_rpow hE (by norm_num)
  rw [max_eq_right (sub_nonpos.mpr hp), zero_pow (by decide)]

private lemma normalized_integrable :
    IntegrableOn (fun E : ℝ => (max (1 - E ^ ((3 : ℝ) / 4)) 0) ^ 2) (Ioi 0) := by
  have hc : Continuous (fun E : ℝ => (max (1 - E ^ ((3 : ℝ) / 4)) 0) ^ 2) :=
    ((continuous_const.sub (Real.continuous_rpow_const (by norm_num))).max continuous_const).pow 2
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  · exact hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact (integrableOn_congr_fun (fun E hE => normalized_tail E hE.le) measurableSet_Ioi).mpr
      integrableOn_zero

private lemma normalized_integral :
    (∫ E in Ioi (0 : ℝ), (max (1 - E ^ ((3 : ℝ) / 4)) 0) ^ 2) = (9 / 35 : ℝ) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    integral_union_eq_left_of_forall measurableSet_Ioi (fun E hE => normalized_tail E hE.le),
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have heq : (∫ E in (0 : ℝ)..1, (max (1 - E ^ ((3 : ℝ) / 4)) 0) ^ 2) =
      ∫ E in (0 : ℝ)..1, (1 - 2 * E ^ ((3 : ℝ) / 4) + E ^ ((3 : ℝ) / 2)) := by
    apply intervalIntegral.integral_congr
    intro E hE
    have hE' : E ∈ Icc (0 : ℝ) 1 := by simpa using hE
    dsimp only
    rw [max_eq_left (sub_nonneg.mpr (Real.rpow_le_one hE'.1 hE'.2 (by norm_num)))]
    have hp : (E ^ ((3 : ℝ) / 4)) ^ 2 = E ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_mul_natCast hE'.1]
      norm_num
    rw [← hp]
    ring
  rw [heq]
  have h34 : IntervalIntegrable (fun E : ℝ => E ^ ((3 : ℝ) / 4)) volume 0 1 :=
    (Real.continuous_rpow_const (by norm_num)).intervalIntegrable _ _
  have h32 : IntervalIntegrable (fun E : ℝ => E ^ ((3 : ℝ) / 2)) volume 0 1 :=
    (Real.continuous_rpow_const (by norm_num)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (intervalIntegrable_const.sub (h34.const_mul 2)) h32,
    intervalIntegral.integral_sub intervalIntegrable_const (h34.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 3 / 4)),
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 3 / 2))]
  norm_num

private lemma rumin_scaling (t d E : ℝ) (ht : 0 ≤ t) (hd : 0 < d) (hE : 0 ≤ E) :
    (max (Real.sqrt t - Real.sqrt d * (((t / d) ^ ((2 : ℝ) / 3)) * E) ^ ((3 : ℝ) / 4)) 0) ^ 2 =
      t * (max (1 - E ^ ((3 : ℝ) / 4)) 0) ^ 2 := by
  have htd : 0 ≤ t / d := div_nonneg ht hd.le
  have hc : Real.sqrt d * ((t / d) ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 4) = Real.sqrt t := by
    rw [← Real.rpow_mul htd]
    norm_num
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div ht d]
    exact mul_div_cancel₀ _ (Real.sqrt_pos.2 hd).ne'
  rw [Real.mul_rpow (Real.rpow_nonneg htd _) hE, ← mul_assoc, hc]
  have hfactor : Real.sqrt t - Real.sqrt t * E ^ ((3 : ℝ) / 4) =
      Real.sqrt t * (1 - E ^ ((3 : ℝ) / 4)) := by ring
  rw [hfactor, ← mul_zero (Real.sqrt t), ← mul_max_of_nonneg _ _ (Real.sqrt_nonneg t),
    mul_pow, Real.sq_sqrt ht]
  simp only [mul_zero]

private lemma rumin_cutoff_value (t d : ℝ) (ht : 0 < t) (hd : 0 < d) :
    ((t / d) ^ ((2 : ℝ) / 3)) * t = d ^ (-(2 : ℝ) / 3) * t ^ ((5 : ℝ) / 3) := by
  rw [Real.div_rpow ht.le hd.le, div_eq_mul_inv, ← Real.rpow_neg hd.le]
  have hp : t ^ ((2 : ℝ) / 3) * t = t ^ ((5 : ℝ) / 3) := by
    calc
      t ^ ((2 : ℝ) / 3) * t = t ^ ((2 : ℝ) / 3) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ ((5 : ℝ) / 3) := by rw [← Real.rpow_add ht]; norm_num
  calc
    t ^ ((2 : ℝ) / 3) * d ^ (-((2 : ℝ) / 3)) * t =
        d ^ (-((2 : ℝ) / 3)) * (t ^ ((2 : ℝ) / 3) * t) := by ring
    _ = d ^ (-(2 : ℝ) / 3) * t ^ ((5 : ℝ) / 3) := by rw [hp]; norm_num

private lemma rumin_joint (t d : ℝ) (ht : 0 ≤ t) (hd : 0 < d) :
    IntegrableOn (fun E : ℝ => (max (Real.sqrt t - Real.sqrt d * E ^ ((3 : ℝ) / 4)) 0) ^ 2) (Ioi 0)
      ∧
      (∫ E in Ioi (0 : ℝ), (max (Real.sqrt t - Real.sqrt d * E ^ ((3 : ℝ) / 4)) 0) ^ 2) =
        (9 / 35 : ℝ) * d ^ (-(2 : ℝ) / 3) * t ^ ((5 : ℝ) / 3) := by
  rcases ht.eq_or_lt with rfl | ht
  · have hzero : ∀ E ∈ Ioi (0 : ℝ),
        (max (Real.sqrt 0 - Real.sqrt d * E ^ ((3 : ℝ) / 4)) 0) ^ 2 = 0 := by
      intro E hE
      rw [Real.sqrt_zero, zero_sub,
        max_eq_right (neg_nonpos.mpr (mul_nonneg (Real.sqrt_nonneg d) (Real.rpow_nonneg hE.le _)))]
      norm_num
    constructor
    · exact (integrableOn_congr_fun hzero measurableSet_Ioi).mpr integrableOn_zero
    · rw [setIntegral_congr_fun measurableSet_Ioi hzero, integral_zero]
      simp only [Real.zero_rpow (by norm_num : (5 : ℝ) / 3 ≠ 0), mul_zero]
  · let e0 : ℝ := (t / d) ^ ((2 : ℝ) / 3)
    have he0 : 0 < e0 := Real.rpow_pos_of_pos (div_pos ht hd) _
    have hscale : (fun E : ℝ => (max (Real.sqrt t - Real.sqrt d * (e0 * E) ^ ((3 : ℝ) / 4)) 0) ^ 2)
      =ᵐ[volume.restrict (Ioi 0)]
        (fun E : ℝ => t * (max (1 - E ^ ((3 : ℝ) / 4)) 0) ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with E hE
      exact rumin_scaling t d E ht.le hd hE.le
    constructor
    · have hi := (normalized_integrable.const_mul t).congr hscale.symm
      have hi' := (integrableOn_Ioi_comp_mul_left_iff
        (fun E : ℝ => (max (Real.sqrt t - Real.sqrt d * E ^ ((3 : ℝ) / 4)) 0) ^ 2) 0 he0).mp hi
      simpa only [mul_zero] using hi'
    · have hchange := integral_comp_mul_left_Ioi'
        (fun E : ℝ => (max (Real.sqrt t - Real.sqrt d * E ^ ((3 : ℝ) / 4)) 0) ^ 2) 0 he0
      simp only [mul_zero, smul_eq_mul] at hchange
      rw [← hchange, integral_congr_ae hscale, integral_const_mul, normalized_integral]
      have hc := rumin_cutoff_value t d ht hd
      calc
        e0 * (t * (9 / 35)) = (9 / 35) * (e0 * t) := by ring
        _ = (9 / 35) * d ^ (-(2 : ℝ) / 3) * t ^ ((5 : ℝ) / 3) := by rw [hc]; ring

/-- The scalar Rumin positive part is integrable on the positive half-line (scalar Rumin
integration). -/
theorem rumin_integrableOn (t d : ℝ) (ht : 0 ≤ t) (hd : 0 < d) :
    IntegrableOn (fun E : ℝ => (max (Real.sqrt t - Real.sqrt d * E ^ ((3 : ℝ) / 4)) 0) ^ 2) (Ioi 0)
      :=
  (rumin_joint t d ht hd).1

/-- Exact scalar Rumin integral, with coefficient `9/35` (scalar Rumin integration). -/
theorem integral_rumin (t d : ℝ) (ht : 0 ≤ t) (hd : 0 < d) :
    (∫ E in Ioi (0 : ℝ), (max (Real.sqrt t - Real.sqrt d * E ^ ((3 : ℝ) / 4)) 0) ^ 2) =
      (9 / 35 : ℝ) * d ^ (-(2 : ℝ) / 3) * t ^ ((5 : ℝ) / 3) :=
  (rumin_joint t d ht hd).2

/-- The nonnegative extended integral equals the same finite scalar value (scalar Rumin
integration). -/
theorem lintegral_rumin (t d : ℝ) (ht : 0 ≤ t) (hd : 0 < d) :
    (∫⁻ E in Ioi (0 : ℝ), ENNReal.ofReal
      ((max (Real.sqrt t - Real.sqrt d * E ^ ((3 : ℝ) / 4)) 0) ^ 2)) =
      ENNReal.ofReal ((9 / 35 : ℝ) * d ^ (-(2 : ℝ) / 3) * t ^ ((5 : ℝ) / 3)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (rumin_integrableOn t d ht hd)
    (Filter.Eventually.of_forall (fun E => sq_nonneg (max (Real.sqrt t - Real.sqrt d * E ^ ((3 : ℝ)
      / 4)) 0))),
    integral_rumin t d ht hd]

/-- The exact Rumin coefficient is strictly positive (the Rumin bound). -/
theorem ruminConstant_pos : 0 < LiebThirring.ruminConstant := by
  unfold LiebThirring.ruminConstant
  exact Real.toNNReal_pos.mpr (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _))
end LiebThirring.Assembly
end
