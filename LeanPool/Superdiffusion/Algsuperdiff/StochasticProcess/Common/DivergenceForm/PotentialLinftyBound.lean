/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PotentialOrder

/-!
# PotentialLinftyBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Uniform bounds for resolvents with potential

A bounded nonnegative potential can only improve the maximum-principle
estimate.  This module records the almost-everywhere absolute bound and its
representative-invariant extended `L∞` formulation.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

/-- If the forcing is almost everywhere bounded in absolute value, the
normalized potential resolvent has the same bound. -/
theorem abs_alpha_mul_potentialResolvent_le_ae (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam Cq : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d → ℝ) (hq : IsBoundedNonnegativePotential U q Cq)
    (f : ScalarL2 U) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, |f x| ≤ C) :
    ∀ᵐ x ∂volumeMeasureOn U,
      |α * potentialResolvent a hα hlam hEll q hq f x| ≤ C  := by
  rcases hC.eq_or_lt with rfl | hCpos
  · have hfzero : f = 0 := by
      apply MeasureTheory.Lp.ext (p := (2 : ENNReal))
      filter_upwards [hf, MeasureTheory.Lp.coeFn_zero (E := ℝ)
        (p := (2 : ENNReal)) (volumeMeasureOn U)] with x hfx hzero
      rw [hzero]
      exact abs_eq_zero.mp (le_antisymm hfx (abs_nonneg _))
    rw [hfzero, map_zero]
    filter_upwards [MeasureTheory.Lp.coeFn_zero (E := ℝ)
      (p := (2 : ENNReal)) (volumeMeasureOn U)] with x hzero
    rw [hzero]
    simp only [Pi.zero_apply, mul_zero, abs_zero, le_refl]
  · let g : ScalarL2 U := C⁻¹ • f
    have hgValue : ∀ᵐ x ∂volumeMeasureOn U, g x = C⁻¹ * f x := by
      filter_upwards [MeasureTheory.Lp.coeFn_smul C⁻¹ f] with x hsmul
      change (C⁻¹ • f) x = C⁻¹ * f x
      simpa only [smul_eq_mul] using! hsmul
    have hgUpper : ∀ᵐ x ∂volumeMeasureOn U, g x ≤ 1 := by
      filter_upwards [hf, hgValue] with x hfx hg
      rw [hg]
      have hfle : f x ≤ C := (le_abs_self _).trans hfx
      calc
        C⁻¹ * f x ≤ C⁻¹ * C :=
          mul_le_mul_of_nonneg_left hfle (inv_nonneg.mpr hCpos.le)
        _ = 1 := inv_mul_cancel₀ hCpos.ne'
    have hnegUpper : ∀ᵐ x ∂volumeMeasureOn U, (-g) x ≤ 1 := by
      filter_upwards [hf, hgValue, MeasureTheory.Lp.coeFn_neg g]
        with x hfx hg hneg
      rw [hneg, Pi.neg_apply, hg]
      have hnegfle : -f x ≤ C := (neg_le_abs _).trans hfx
      calc
        -(C⁻¹ * f x) = C⁻¹ * (-f x) := by ring
        _ ≤ C⁻¹ * C :=
          mul_le_mul_of_nonneg_left hnegfle (inv_nonneg.mpr hCpos.le)
        _ = 1 := inv_mul_cancel₀ hCpos.ne'
    have hgBound := alpha_mul_potentialResolvent_le_one_ae
      a hU hα hlam hEll q hq g hgUpper
    have hnegBound := alpha_mul_potentialResolvent_le_one_ae
      a hU hα hlam hEll q hq (-g) hnegUpper
    have hmapG : potentialResolvent a hα hlam hEll q hq g =
        C⁻¹ • potentialResolvent a hα hlam hEll q hq f := by
      change potentialResolvent a hα hlam hEll q hq (C⁻¹ • f) = _
      rw [map_smul]
    have hmapNeg : potentialResolvent a hα hlam hEll q hq (-g) =
        -(potentialResolvent a hα hlam hEll q hq g) := by
      rw [map_neg]
    filter_upwards [hgBound, hnegBound,
      MeasureTheory.Lp.coeFn_smul C⁻¹
        (potentialResolvent a hα hlam hEll q hq f),
      MeasureTheory.Lp.coeFn_neg
        (potentialResolvent a hα hlam hEll q hq g)]
        with x hxUpper hxNeg hsmul hneg
    rw [hmapG, hsmul] at hxUpper
    rw [hmapNeg, hneg, hmapG] at hxNeg
    simp only [Pi.neg_apply] at hxNeg
    rw [hsmul] at hxNeg
    simp only [Pi.smul_apply, smul_eq_mul] at hxUpper
    rw [abs_le]
    constructor
    · have hnegResult :
          -(α * potentialResolvent a hα hlam hEll q hq f x) ≤ C := by
        calc
          -(α * potentialResolvent a hα hlam hEll q hq f x) =
              C * (α * (-(C⁻¹ *
                potentialResolvent a hα hlam hEll q hq f x))) := by
            field_simp
          _ ≤ C * 1 := mul_le_mul_of_nonneg_left hxNeg hC
          _ = C := mul_one C
      calc
        -C ≤ -(-(α * potentialResolvent a hα hlam hEll q hq f x)) :=
          neg_le_neg hnegResult
        _ = α * potentialResolvent a hα hlam hEll q hq f x := neg_neg _
    · calc
        α * potentialResolvent a hα hlam hEll q hq f x =
            C * (α * (C⁻¹ *
              potentialResolvent a hα hlam hEll q hq f x)) := by
          field_simp
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hxUpper hC
        _ = C := mul_one C

end DivergenceFormProcess.Form
