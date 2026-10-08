/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.WeightedNonnegativeKernelSchur

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A weighted Schur test for nonnegative kernels

This is the conjugated form of the nonnegative-kernel Schur test. Separate
positive finite weights on the source and target permit row and column bounds
that scale with distance to a boundary.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem lintegral_mul_rpow_two_le
    {β : Type*} [MeasurableSpace β] (ν : Measure β)
    {w f : β → ℝ≥0∞} (hw : AEMeasurable w ν) (hf : AEMeasurable f ν) :
    (∫⁻ y, w y * f y ∂ν) ^ (2 : ℝ) ≤
      (∫⁻ y, w y ∂ν) * ∫⁻ y, w y * f y ^ (2 : ℝ) ∂ν := by
  have hwf : AEMeasurable (fun y => w y * f y ^ (2 : ℝ)) ν :=
    hw.mul (hf.pow_const (2 : ℝ))
  have hholder := ENNReal.lintegral_mul_norm_pow_le
    (μ := ν) (f := w) (g := fun y => w y * f y ^ (2 : ℝ))
    hw hwf (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hleft :
      (∫⁻ y, w y ^ (1 / 2 : ℝ) *
          (w y * f y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ∂ν) =
        ∫⁻ y, w y * f y ∂ν := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    rw [← mul_assoc,
      ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ)
        (by norm_num) (by norm_num)]
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hleft] at hholder
  have hsquare := ENNReal.rpow_le_rpow hholder (by norm_num : 0 ≤ (2 : ℝ))
  calc
    (∫⁻ y, w y * f y ∂ν) ^ (2 : ℝ)
        ≤ ((∫⁻ y, w y ∂ν) ^ (1 / 2 : ℝ) *
            (∫⁻ y, w y * f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
      hsquare
    _ = (∫⁻ y, w y ∂ν) * ∫⁻ y, w y * f y ^ (2 : ℝ) ∂ν := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ))]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

private theorem lintegral_weighted_mul_rpow_two_le
    {β : Type*} [MeasurableSpace β] (ν : Measure β)
    {w f q : β → ℝ≥0∞}
    (hw : AEMeasurable w ν) (hf : AEMeasurable f ν)
    (hq : AEMeasurable q ν)
    (hq0 : ∀ y, q y ≠ 0) (hqtop : ∀ y, q y ≠ ⊤) :
    (∫⁻ y, w y * f y ∂ν) ^ (2 : ℝ) ≤
      (∫⁻ y, w y * q y ∂ν) *
        ∫⁻ y, w y * (f y ^ (2 : ℝ) / q y) ∂ν := by
  have hwq : AEMeasurable (fun y => w y * q y) ν := hw.mul hq
  have hfq : AEMeasurable (fun y => f y / q y) ν := hf.div hq
  have hleft : (∫⁻ y, (w y * q y) * (f y / q y) ∂ν) =
      ∫⁻ y, w y * f y ∂ν := by
    refine lintegral_congr fun y => ?_
    rw [mul_assoc, ENNReal.mul_div_cancel (hq0 y) (hqtop y)]
  have hbase := lintegral_mul_rpow_two_le ν hwq hfq
  calc
    (∫⁻ y, w y * f y ∂ν) ^ (2 : ℝ) =
        (∫⁻ y, (w y * q y) * (f y / q y) ∂ν) ^ (2 : ℝ) := by rw [hleft]
    _ ≤ (∫⁻ y, w y * q y ∂ν) *
          ∫⁻ y, (w y * q y) * (f y / q y) ^ (2 : ℝ) ∂ν := hbase
    _ = (∫⁻ y, w y * q y ∂ν) *
          ∫⁻ y, w y * (f y ^ (2 : ℝ) / q y) ∂ν := by
      congr 1
      refine lintegral_congr fun y => ?_
      rw [ENNReal.rpow_two, ENNReal.rpow_two]
      calc
        w y * q y * (f y / q y) ^ 2 =
            w y * (q y * (f y / q y)) * (f y / q y) := by ring
        _ = w y * f y * (f y / q y) := by
          rw [ENNReal.mul_div_cancel (hq0 y) (hqtop y)]
        _ = w y * (f y ^ 2 / q y) := by
          rw [pow_two, mul_div_assoc]
          ring

/-- Weighted squared `L²` Schur test. The target weight `p` and source
weight `q` need only be positive and finite; no integrability hypothesis on
the input is required. -/
theorem lintegral_weightedNonnegativeKernel_rpow_two_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    {K : α → β → ℝ≥0∞} {f : β → ℝ≥0∞}
    {p : α → ℝ≥0∞} {q : β → ℝ≥0∞} {A B : ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hf : Measurable f)
    (hp : Measurable p) (hq : Measurable q)
    (hq0 : ∀ y, q y ≠ 0) (hqtop : ∀ y, q y ≠ ⊤)
    (hrow : ∀ᵐ x ∂μ, ∫⁻ y, K x y * q y ∂ν ≤ A * p x)
    (hcol : ∀ᵐ y ∂ν, ∫⁻ x, K x y * p x ∂μ ≤ B * q y) :
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℝ) ∂μ) ≤
      A * B * ∫⁻ y, f y ^ (2 : ℝ) ∂ν := by
  have hKfq : Measurable
      (Function.uncurry fun x y => K x y * (f y ^ (2 : ℝ) / q y)) := by
    rw [show (Function.uncurry fun x y => K x y * (f y ^ (2 : ℝ) / q y)) =
        (Function.uncurry K * fun z : α × β =>
          (f z.2 ^ (2 : ℝ) / q z.2)) from by
      funext z; rfl]
    exact hK.mul (((hf.comp measurable_snd).pow_const (2 : ℝ)).div
      (hq.comp measurable_snd))
  have hpoint :
      ∀ᵐ x ∂μ, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℝ) ≤
        A * p x * ∫⁻ y, K x y * (f y ^ (2 : ℝ) / q y) ∂ν := by
    filter_upwards [hrow] with x hx
    have hKx : AEMeasurable (K x) ν := by
      rw [show K x = (Function.uncurry K) ∘ (fun y => (x, y)) from by
        funext y; rfl]
      exact (hK.comp measurable_prodMk_left).aemeasurable
    exact (lintegral_weighted_mul_rpow_two_le ν hKx hf.aemeasurable
      hq.aemeasurable hq0 hqtop).trans (mul_le_mul_left hx _)
  have hcolWeighted :
      ∀ᵐ y ∂ν, (∫⁻ x, K x y * p x * (f y ^ (2 : ℝ) / q y) ∂μ) ≤
        B * f y ^ (2 : ℝ) := by
    filter_upwards [hcol] with y hy
    have hKpy : Measurable (fun x => K x y * p x) := by
      have hKy : Measurable (fun x => K x y) := by
        rw [show (fun x => K x y) = (Function.uncurry K) ∘ (fun x => (x, y)) from by
          funext x; rfl]
        exact hK.comp measurable_prodMk_right
      exact hKy.mul hp
    rw [lintegral_mul_const _ hKpy]
    calc
      (∫⁻ x, K x y * p x ∂μ) * (f y ^ (2 : ℝ) / q y)
          ≤ (B * q y) * (f y ^ (2 : ℝ) / q y) :=
        mul_le_mul_left hy _
      _ = B * f y ^ (2 : ℝ) := by
        rw [mul_assoc, ENNReal.mul_div_cancel (hq0 y) (hqtop y)]
  calc
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℝ) ∂μ)
        ≤ ∫⁻ x, A * (p x *
            ∫⁻ y, K x y * (f y ^ (2 : ℝ) / q y) ∂ν) ∂μ := by
      refine lintegral_mono_ae (hpoint.mono fun x hx => ?_)
      simpa only [mul_assoc] using hx
    _ = A * ∫⁻ x, p x *
          ∫⁻ y, K x y * (f y ^ (2 : ℝ) / q y) ∂ν ∂μ := by
      exact lintegral_const_mul A (hp.mul hKfq.lintegral_prod_right)
    _ = A * ∫⁻ x, ∫⁻ y,
          K x y * p x * (f y ^ (2 : ℝ) / q y) ∂ν ∂μ := by
      congr 1
      refine lintegral_congr fun x => ?_
      calc
        p x * ∫⁻ y, K x y * (f y ^ (2 : ℝ) / q y) ∂ν =
            ∫⁻ y, p x * (K x y * (f y ^ (2 : ℝ) / q y)) ∂ν := by
          exact (lintegral_const_mul (p x)
            ((hK.comp measurable_prodMk_left).mul
              ((hf.pow_const (2 : ℝ)).div hq))).symm
        _ = ∫⁻ y, K x y * p x * (f y ^ (2 : ℝ) / q y) ∂ν := by
          refine lintegral_congr fun y => ?_
          ring
    _ = A * ∫⁻ y, ∫⁻ x,
          K x y * p x * (f y ^ (2 : ℝ) / q y) ∂μ ∂ν := by
      have hswap : Measurable (Function.uncurry fun x y =>
          K x y * p x * (f y ^ (2 : ℝ) / q y)) := by
        rw [show (Function.uncurry fun x y =>
            K x y * p x * (f y ^ (2 : ℝ) / q y)) =
            ((Function.uncurry K * fun z : α × β => p z.1) *
              fun z : α × β => f z.2 ^ (2 : ℝ) / q z.2) from by
          funext z; rfl]
        exact (hK.mul (hp.comp measurable_fst)).mul
          (((hf.comp measurable_snd).pow_const (2 : ℝ)).div
            (hq.comp measurable_snd))
      rw [lintegral_lintegral_swap hswap.aemeasurable]
    _ ≤ A * ∫⁻ y, B * f y ^ (2 : ℝ) ∂ν := by
      exact mul_le_mul_right (lintegral_mono_ae hcolWeighted) A
    _ = A * (B * ∫⁻ y, f y ^ (2 : ℝ) ∂ν) := by
      rw [lintegral_const_mul B (hf.pow_const (2 : ℝ))]
    _ = A * B * ∫⁻ y, f y ^ (2 : ℝ) ∂ν := by
      rw [mul_assoc]

end

end HighContrast
end HCPolySupport
