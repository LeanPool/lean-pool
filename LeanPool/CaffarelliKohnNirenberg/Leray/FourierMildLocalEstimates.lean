/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildIntegral
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalParameters
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Abel estimates for the local regularized mild map

The translated Stokes integral has the square-root time bound used in
lem:reg-local-mild.
-/

public section

open MeasureTheory Filter
open scoped Interval ENNReal

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

private theorem regularizedMildAbelKernel_integral (T : ℝ) :
    ∫ τ in (0 : ℝ)..T, τ ^ (-(2 : ℝ)⁻¹) = 2 * Real.sqrt T := by
  have hformula := integral_rpow
    (a := (0 : ℝ)) (b := T) (r := -(2 : ℝ)⁻¹)
    (Or.inl (by norm_num : (-1 : ℝ) < -(2 : ℝ)⁻¹))
  rw [hformula]
  have hzero : (0 : ℝ) ^ (-(2 : ℝ)⁻¹ + 1) = 0 := by
    apply Real.zero_rpow
    norm_num
  have hpow : T ^ (-(2 : ℝ)⁻¹ + 1) = Real.sqrt T := by
    rw [show -(2 : ℝ)⁻¹ + 1 = (1 / 2 : ℝ) by norm_num,
      ← Real.sqrt_eq_rpow T]
  rw [hzero, hpow]
  field_simp
  ring

/-- The translated Stokes term is bounded by the Abel integral of a uniform
tensor bound. -/
theorem mildShiftedStokesIntegral_norm_le
    (F : ℝ → RealTensorL2) (C : ℝ)
    (hFC : ∀ s, ‖F s‖ ≤ C) (hC : 0 ≤ C) (T t : ℝ) (hT : 0 ≤ T) :
    ‖∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t τ‖ ≤
      2 * (C / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T := by
  let B : ℝ := C / Real.sqrt (2 * Real.exp 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hkernelBase : IntervalIntegrable
      (fun τ : ℝ => τ ^ (-(2 : ℝ)⁻¹)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hkernel : IntervalIntegrable
      (fun τ : ℝ => B * τ ^ (-(2 : ℝ)⁻¹)) volume 0 T :=
    hkernelBase.const_mul B
  have hscalarOn : IntegrableOn
      (fun τ : ℝ => B * τ ^ (-(2 : ℝ)⁻¹)) (Set.Ioc 0 T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hkernel
  have hpoint : ∀ᵐ τ ∂(volume.restrict (Set.Ioc 0 T)),
      ‖mildShiftedStokesIntegrand F t τ‖ ≤ B * τ ^ (-(2 : ℝ)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    have hτpos : 0 < τ := (Set.mem_Ioc.mp hτ).1
    by_cases h : 0 < τ ∧ τ < t
    · simp only [mildShiftedStokesIntegrand, h, and_self, ↓reduceDIte,
        ge_iff_le]
      have hop := realStokesOperator_norm_le h.1 (F (t - τ))
      have hkernelIdentity :
          1 / Real.sqrt (2 * Real.exp 1 * τ) =
            (1 / Real.sqrt (2 * Real.exp 1)) *
              τ ^ (-(2 : ℝ)⁻¹) := by
        have hconst : 0 ≤ 2 * Real.exp 1 := by positivity
        rw [show 2 * Real.exp 1 * τ = (2 * Real.exp 1) * τ by ring,
          Real.sqrt_mul hconst τ]
        have hsqrt : Real.sqrt τ = τ ^ (1 / 2 : ℝ) :=
          Real.sqrt_eq_rpow _
        rw [hsqrt, Real.rpow_neg (le_of_lt hτpos)]
        field_simp
      calc
        ‖realStokesOperator h.1 (F (t - τ))‖ ≤
            (1 / Real.sqrt (2 * Real.exp 1 * τ)) *
              ‖F (t - τ)‖ := hop
        _ ≤ (1 / Real.sqrt (2 * Real.exp 1 * τ)) * C :=
          mul_le_mul_of_nonneg_left (hFC _) (by positivity)
        _ = B * τ ^ (-(2 : ℝ)⁻¹) := by
          rw [hkernelIdentity]
          dsimp [B]
          ring
    · simpa [mildShiftedStokesIntegrand, h] using
        mul_nonneg hB (Real.rpow_nonneg (le_of_lt hτpos) _)
  have hsetNorm := norm_integral_le_of_norm_le hscalarOn hpoint
  have hsetEq :
      (∫ τ in Set.Ioc (0 : ℝ) T, mildShiftedStokesIntegrand F t τ) =
        ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t τ := by
    symm
    exact intervalIntegral.integral_of_le hT
  have hkernelIntegral := regularizedMildAbelKernel_integral T
  calc
    ‖∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t τ‖ =
        ‖∫ τ in Set.Ioc (0 : ℝ) T, mildShiftedStokesIntegrand F t τ‖ := by
          rw [hsetEq]
    _ ≤ ∫ τ in Set.Ioc (0 : ℝ) T,
        B * τ ^ (-(2 : ℝ)⁻¹) := hsetNorm
    _ = ∫ τ in (0 : ℝ)..T, B * τ ^ (-(2 : ℝ)⁻¹) := by
          symm
          exact intervalIntegral.integral_of_le hT
    _ = B * ∫ τ in (0 : ℝ)..T, τ ^ (-(2 : ℝ)⁻¹) := by
          rw [intervalIntegral.integral_const_mul]
    _ = 2 * (C / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T := by
          rw [hkernelIntegral]
          dsimp [B]
          ring


end CKN.Leray

end
