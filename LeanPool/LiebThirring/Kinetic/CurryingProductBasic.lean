/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Tonelli and seminorms for L² currying

Tonelli and seminorm identities for product-space L² currying.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}

/-- L² mass in extended norm form, valid for arbitrary normed targets. -/
theorem lintegral_l2_enorm_sq (u : Lp E 2 μ) :
    (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ) = ‖u‖ₑ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0))
    (by norm_num) (Lp.aestronglyMeasurable u)
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
    ← Lp.enorm_def] using h.symm

/-- The L² seminorm of a strongly measurable slice is a Tonelli formula. -/
theorem l2_slice_eLpNorm_eq (f : α × β → E) (hf : StronglyMeasurable f) (x : α) :
    eLpNorm (fun y => f (x, y)) 2 ν =
      (∫⁻ y, ‖f (x, y)‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  have hm : AEStronglyMeasurable (fun y => f (x, y)) ν :=
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hm

/-- Slice seminorms are measurable, even before slices are known to be L². -/
theorem measurable_l2_slice_eLpNorm [SFinite ν] (f : α × β → E)
    (hf : StronglyMeasurable f) :
    Measurable (fun x => eLpNorm (fun y => f (x, y)) 2 ν) := by
  simp_rw [l2_slice_eLpNorm_eq f hf]
  exact (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).measurable.comp
    ((hf.enorm.pow_const 2).lintegral_prod_right')

/-- A product L² function has L² slices on almost every outer coordinate. -/
theorem memLp_l2_slice_ae [SFinite ν] (f : α × β → E)
    (hf : StronglyMeasurable f) (hLp : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => f (x, y)) 2 ν := by
  have hm : Measurable (fun x => ∫⁻ y, ‖f (x, y)‖ₑ ^ 2 ∂ν) :=
    (hf.enorm.pow_const 2).lintegral_prod_right'
  have hmass : (∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ^ 2 ∂ν ∂μ) < ⊤ := by
    rw [← lintegral_prod _ (hf.enorm.pow_const 2).aemeasurable]
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hLp
  filter_upwards [ae_lt_top hm hmass.ne] with x hx
  have hsm : AEStronglyMeasurable (fun y => f (x, y)) ν :=
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hsm).mpr
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using hx

end LiebThirring

end
