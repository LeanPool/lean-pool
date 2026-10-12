/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Nonnegative integral Gram kernels

Extended Cauchy–Schwarz, including zero and infinite diagonal integrals.

The energy of an integral Gram kernel is itself an integral Gram pairing of potentials.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring

/-- Extended Cauchy–Schwarz, including zero and infinite diagonal integrals. -/
theorem lintegral_mul_sq_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ z, f z * g z ∂ν) ^ 2 ≤ (∫⁻ z, f z ^ 2 ∂ν) * (∫⁻ z, g z ^ 2 ∂ν) := by
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hconj hf.aemeasurable hg.aemeasurable
  have hsq := pow_le_pow_left' h 2
  have hroot (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  simpa only [Pi.mul_apply, ENNReal.rpow_two, mul_pow, hroot] using hsq

/-- The energy of an integral Gram kernel is itself an integral Gram pairing of potentials. -/
theorem lintegral_gram_pairing {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (α β : Measure X) (ν : Measure Ω) [SFinite α] [SFinite β] [SFinite ν]
    (f : X → Ω → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    (∫⁻ x, ∫⁻ y, ∫⁻ z, f x z * f y z ∂ν ∂β ∂α) =
      ∫⁻ z, (∫⁻ x, f x z ∂α) * (∫⁻ y, f y z ∂β) ∂ν := by
  have hfx (x : X) : Measurable (f x) := hf.of_uncurry_left
  have hxy (z : Ω) : Measurable (fun x : X => f x z) := hf.of_uncurry_right
  have hinner (x : X) :
      (∫⁻ y, ∫⁻ z, f x z * f y z ∂ν ∂β) =
        ∫⁻ z, f x z * (∫⁻ y, f y z ∂β) ∂ν := by
    rw [lintegral_lintegral_swap (by fun_prop)]
    apply lintegral_congr
    intro z
    exact lintegral_const_mul _ (hxy z)
  simp_rw [hinner]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro z
  exact lintegral_mul_const _ (hxy z)

end LiebThirring

end
