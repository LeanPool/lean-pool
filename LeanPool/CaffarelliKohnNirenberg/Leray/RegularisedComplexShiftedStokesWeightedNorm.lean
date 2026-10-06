/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedComplexShiftedStokesIntegrability
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedComplexAbelWeight

/-!
# Weighted complex physical Stokes bound

An exponential weight makes the linear Volterra operator small on a fixed
finite interval, independent of its length.
-/

public section

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- A tensor path controlled by an exponential weight has a translated
Stokes integral controlled by the same weight and the Gamma kernel. -/
theorem regularisedComplexShiftedStokesIntegral_weighted_norm_le
    (F : ℝ → ComplexTensorL2) (T t M lam : ℝ)
    (hT : 0 ≤ T) (ht : t ≤ T) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hF : ∀ s, 0 ≤ s → s ≤ T →
      ‖F s‖ ≤ M * Real.exp (lam * s)) :
    ‖∫ τ in (0 : ℝ)..T,
        regularisedComplexShiftedStokesIntegrand F t τ‖ ≤
      M / Real.sqrt (2 * Real.exp 1) * Real.exp (lam * t) *
        (lam ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2)) := by
  let D : ℝ := M / Real.sqrt (2 * Real.exp 1) * Real.exp (lam * t)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbase : IntegrableOn
      (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ))
      (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := -(1 / 2 : ℝ)) (p := 1) (b := lam)
      (by norm_num) one_pos hlam
    simpa only [Real.rpow_one, div_one, mul_one] using h
  have hkernel : IntegrableOn
      (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ))
      (Ioc 0 T) := hbase.mono_set Ioc_subset_Ioi_self
  have hmajorant : IntegrableOn
      (fun τ : ℝ => D * (τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ)))
      (Ioc 0 T) := hkernel.const_mul D
  have hpoint : ∀ᵐ τ ∂(volume.restrict (Ioc 0 T)),
      ‖regularisedComplexShiftedStokesIntegrand F t τ‖ ≤
        D * (τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    have hτpos : 0 < τ := hτ.1
    by_cases h : 0 < τ ∧ τ < t
    · simp only [regularisedComplexShiftedStokesIntegrand, dite_eq_left h]
      have hop := stokesL2Operator_norm_le h.1 (F (t - τ))
      have hk : 0 ≤ (1 / Real.sqrt (2 * Real.exp 1)) *
          τ ^ (-(1 / 2 : ℝ)) := by positivity
      calc
        ‖stokesL2Operator h.1 (F (t - τ))‖ ≤
            (1 / Real.sqrt (2 * Real.exp 1 * τ)) * ‖F (t - τ)‖ := hop
        _ = ((1 / Real.sqrt (2 * Real.exp 1)) *
            τ ^ (-(1 / 2 : ℝ))) * ‖F (t - τ)‖ := by
              rw [stokes_kernel_eq_rpow hτpos]
        _ ≤ ((1 / Real.sqrt (2 * Real.exp 1)) *
            τ ^ (-(1 / 2 : ℝ))) * (M * Real.exp (lam * (t - τ))) :=
              mul_le_mul_of_nonneg_left
                (hF _ (sub_nonneg.mpr h.2.le)
                  (by linarith only [hτpos, ht])) hk
        _ = D * (τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ)) := by
              rw [show lam * (t - τ) = lam * t + -lam * τ by ring,
                Real.exp_add]
              dsimp [D]
              ring
    · simp only [regularisedComplexShiftedStokesIntegrand, dite_eq_right h, norm_zero]
      exact mul_nonneg hD
        (mul_nonneg (Real.rpow_nonneg hτpos.le _) (Real.exp_pos _).le)
  have hbound := norm_integral_le_of_norm_le hmajorant hpoint
  have hGamma := regularisedAbelElapsedExpIntegral_le (T := T) hlam
  have hfactor :
      ∫ τ in Ioc 0 T,
          D * (τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ)) =
        D * ∫ τ in Ioc 0 T,
          τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ) := by
    rw [integral_const_mul]
  calc
    ‖∫ τ in (0 : ℝ)..T,
        regularisedComplexShiftedStokesIntegrand F t τ‖ =
      ‖∫ τ in Ioc 0 T,
        regularisedComplexShiftedStokesIntegrand F t τ‖ := by
          rw [intervalIntegral.integral_of_le hT]
    _ ≤ ∫ τ in Ioc 0 T,
        D * (τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ)) := hbound
    _ = D * ∫ τ in Ioc 0 T,
        τ ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * τ) := hfactor
    _ ≤ D * (lam ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2)) :=
      mul_le_mul_of_nonneg_left hGamma hD
    _ = _ := rfl

end CKN.Leray

end
