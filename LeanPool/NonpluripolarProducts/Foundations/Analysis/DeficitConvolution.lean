/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.WeightedDiscSubmean
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.TranslationPairing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.CircleMeanSecondOrder

/-!
# Smooth supermeans obtained from singular deficits

The nonnegative Tonelli inequality is first translated by Haar invariance.
Only then is the extended deficit replaced by its almost-everywhere equal
real density. This gives supermean inequalities for one actual smooth scalar
pairing, and therefore a nonpositive Levi pairing.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory Laplacian
open scoped ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant]

omit [NormedSpace ℝ E] [SFinite μ] in
/-- Translation turns an extended weighted deficit integral into the actual
scalar pairing with its nonnegative real representative. The representative
is required to agree only almost everywhere. -/
theorem lintegral_deficit_translate_eq_ofReal_pairing
    {D : E → ℝ≥0∞} {f φ : E → ℝ}
    (hD : D =ᵐ[μ] fun x => ENNReal.ofReal (f x))
    (hf : LocallyIntegrable f μ) (hfn : ∀ x, 0 ≤ f x)
    (hφs : HasCompactSupport φ) (hφ : Continuous φ) (hφn : ∀ x, 0 ≤ φ x)
    (a : E) :
    ∫⁻ x, ENNReal.ofReal (φ x) * D (x + a) ∂μ =
      ENNReal.ofReal (translationPairing μ f φ a) := by
  have htrans := (measurePreserving_add_right μ a).lintegral_comp_emb
    (MeasurableEquiv.addRight a).measurableEmbedding
    (fun y => ENNReal.ofReal (φ (y - a)) * D y)
  calc
    (∫⁻ x, ENNReal.ofReal (φ x) * D (x + a) ∂μ) =
        ∫⁻ y, ENNReal.ofReal (φ (y - a)) * D y ∂μ := by
      simpa only [add_sub_cancel_right] using htrans
    _ = ∫⁻ y, ENNReal.ofReal (f y * φ (y - a)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hD] with y hy
      rw [hy, ENNReal.ofReal_mul (hfn y), mul_comm]
    _ = ENNReal.ofReal (translationPairing μ f φ a) :=
      (ofReal_integral_eq_lintegral_ofReal
        (integrable_translationPairing hf hφs hφ a)
        (ae_of_all _ (fun y => mul_nonneg (hfn y) (hφn (y - a))))).symm

/-- For a continuous nonnegative function, an extended angular integral bound
is exactly the corresponding ordinary circle-average upper bound. -/
theorem circleAverage_le_of_lintegral_ofReal_le {h : ℂ → ℝ}
    (hh : Continuous h) (hn : ∀ z, 0 ≤ h z) (r : ℝ)
    (hm : (∫⁻ t in Ioc 0 (2 * Real.pi), ENNReal.ofReal (h (circleMap 0 r t))) ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (h 0)) :
    Real.circleAverage h 0 r ≤ h 0 := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hi : IntervalIntegrable (fun t : ℝ => h (circleMap 0 r t)) volume
      0 (2 * Real.pi) := (hh.comp (by fun_prop)).intervalIntegrable _ _
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1
    (ae_of_all _ (fun t => hn (circleMap 0 r t))),
    ← intervalIntegral.integral_of_le hp.le,
    ← ENNReal.ofReal_mul hp.le,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hp.le (hn 0))] at hm
  simp only [Real.circleAverage, smul_eq_mul]
  rw [← div_eq_inv_mul, div_le_iff₀ hp]
  simpa only [mul_comm] using hm

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- The smooth pairing with a real representative of a singular deficit
satisfies the supermean inequality whenever the weighted discs are admissible.
Only the disc submean inequality and measurability of the localized deficit
are used. -/
theorem HasDiscSubmeanOn.circleAverage_deficit_pairing_le {u : E → EReal} {U K : Set E}
    (hu : HasDiscSubmeanOn u U) (hKU : K ⊆ U) (C : ℝ)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal))
    (hDm : Measurable (K.indicator (fun y => ((C : EReal) - u y).toENNReal))) {f φ : E → ℝ}
    (hD : K.indicator (fun y => ((C : EReal) - u y).toENNReal) =ᵐ[μ]
      fun y => ENNReal.ofReal (f y))
    (hf : LocallyIntegrable f μ) (hfn : ∀ x, 0 ≤ f x)
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ) (hφn : ∀ x, 0 ≤ φ x)
    (v : E) {r : ℝ} (hr : 0 < r)
    (hdisc : ∀ x ∈ Function.support φ, affineClosedDisc x v r ⊆ K) :
    Real.circleAverage (fun z : ℂ => translationPairing μ f φ (z • v)) 0 r ≤
      translationPairing μ f φ 0 := by
  have hm := hu.weighted_circle_deficit_le μ hKU C hC hDm
    (hφ.continuous.measurable.ennreal_ofReal) v hr (by
      intro x hx
      apply hdisc x
      intro hx0
      exact hx (by simp [hx0]))
  have hinner (a : E) := lintegral_deficit_translate_eq_ofReal_pairing
    hD hf hfn hφs hφ.continuous hφn a
  have hzero : (∫⁻ x, ENNReal.ofReal (φ x) *
      K.indicator (fun y => ((C : EReal) - u y).toENNReal) x ∂μ) =
        ENNReal.ofReal (translationPairing μ f φ 0) := by
    simpa only [add_zero] using hinner 0
  simp_rw [hinner] at hm
  rw [hzero] at hm
  have hn (z : ℂ) : 0 ≤ translationPairing μ f φ (z • v) :=
    integral_nonneg (fun x => mul_nonneg (hfn x) (hφn (x - z • v)))
  simpa only [zero_smul] using circleAverage_le_of_lintegral_ofReal_le
    (contDiff_translationPairing_complexLine hf hφs hφ v).continuous hn r
      (by simpa only [zero_smul] using hm)

/-- A circle supermean bound for the translated pairing implies a nonpositive Levi pairing. -/
theorem integral_mul_leviForm_nonpos_of_circleAverage_le
    {f φ : E → ℝ} (hf : LocallyIntegrable f μ)
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ)
    (v : E) {R : ℝ} (hR : 0 < R)
    (haverage : ∀ r ∈ Ioo 0 R,
      Real.circleAverage (fun z : ℂ => translationPairing μ f φ (z • v)) 0 r ≤
        translationPairing μ f φ 0) :
    (∫ x, f x * leviForm φ x v ∂μ) ≤ 0 := by
  let h : ℂ → ℝ := fun z => translationPairing μ f φ (z • v)
  have hh : ContDiff ℝ 2 h := contDiff_translationPairing_complexLine hf hφs hφ v
  have hmean (r : ℝ) (hr : r ∈ Ioo 0 R) : (-h) 0 ≤ Real.circleAverage (-h) 0 r := by
    have hm := haverage r hr
    have hneg : Real.circleAverage (-h) 0 r = -Real.circleAverage h 0 r := by
      simpa only [neg_one_smul] using
        (Real.circleAverage_smul (f := h) (c := 0) (R := r) (a := (-1 : ℝ)))
    rw [hneg]
    simpa only [h, Pi.neg_apply, zero_smul] using neg_le_neg hm
  have hΔ := laplacian_nonneg_of_circleAverage_submean hh.neg 0 hR hmean
  have hline := laplacian_complexLine (contDiff_translationPairing hf hφs hφ)
    (0 : E) v (0 : ℂ)
  simp only [zero_add, zero_smul] at hline
  rw [leviForm_translationPairing hf hφs hφ] at hline
  simp only [sub_zero] at hline
  change 0 ≤ Δ (-h) 0 at hΔ
  rw [InnerProductSpace.laplacian_neg, Pi.neg_apply] at hΔ
  change 0 ≤ -Δ (fun z : ℂ => translationPairing μ f φ (z • v)) 0 at hΔ
  rw [hline] at hΔ
  linarith

/-- A uniform admissible family of weighted discs forces the actual Levi
pairing of the localized deficit to be nonpositive. Only the disc submean
inequality and measurability of the localized deficit are used. -/
theorem HasDiscSubmeanOn.integral_deficit_mul_leviForm_nonpos {u : E → EReal} {U K : Set E}
    (hu : HasDiscSubmeanOn u U) (hKU : K ⊆ U) (C : ℝ)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal))
    (hDm : Measurable (K.indicator (fun y => ((C : EReal) - u y).toENNReal))) {f φ : E → ℝ}
    (hD : K.indicator (fun y => ((C : EReal) - u y).toENNReal) =ᵐ[μ]
      fun y => ENNReal.ofReal (f y))
    (hf : LocallyIntegrable f μ) (hfn : ∀ x, 0 ≤ f x)
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ) (hφn : ∀ x, 0 ≤ φ x)
    (v : E) {R : ℝ} (hR : 0 < R)
    (hdisc : ∀ r ∈ Ioo 0 R, ∀ x ∈ Function.support φ, affineClosedDisc x v r ⊆ K) :
    (∫ x, f x * leviForm φ x v ∂μ) ≤ 0 :=
  integral_mul_leviForm_nonpos_of_circleAverage_le hf hφs hφ v hR fun r hr =>
    hu.circleAverage_deficit_pairing_le hKU C hC hDm hD hf hfn hφs hφ hφn v hr.1 (hdisc r hr)

/-- The smooth pairing with a real representative of a singular deficit
satisfies the supermean inequality whenever the weighted discs are admissible. -/
theorem DiscPshOn.circleAverage_deficit_pairing_le {u : E → EReal} {U K : Set E}
    (hu : DiscPshOn u U) (hK : MeasurableSet K) (hKU : K ⊆ U) (C : ℝ)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal)) {f φ : E → ℝ}
    (hD : K.indicator (fun y => ((C : EReal) - u y).toENNReal) =ᵐ[μ]
      fun y => ENNReal.ofReal (f y))
    (hf : LocallyIntegrable f μ) (hfn : ∀ x, 0 ≤ f x)
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ) (hφn : ∀ x, 0 ≤ φ x)
    (v : E) {r : ℝ} (hr : 0 < r)
    (hdisc : ∀ x ∈ Function.support φ, affineClosedDisc x v r ⊆ K) :
    Real.circleAverage (fun z : ℂ => translationPairing μ f φ (z • v)) 0 r ≤
      translationPairing μ f φ 0 :=
  hu.submean.circleAverage_deficit_pairing_le hKU C hC
    (hu.measurable_indicator_deficit hK hKU C) hD hf hfn hφs hφ hφn v hr hdisc

/-- A uniform admissible family of weighted discs forces the actual Levi
pairing of the localized deficit to be nonpositive. -/
theorem DiscPshOn.integral_deficit_mul_leviForm_nonpos {u : E → EReal} {U K : Set E}
    (hu : DiscPshOn u U) (hK : MeasurableSet K) (hKU : K ⊆ U) (C : ℝ)
    (hC : ∀ y ∈ K, u y ≤ (C : EReal)) {f φ : E → ℝ}
    (hD : K.indicator (fun y => ((C : EReal) - u y).toENNReal) =ᵐ[μ]
      fun y => ENNReal.ofReal (f y))
    (hf : LocallyIntegrable f μ) (hfn : ∀ x, 0 ≤ f x)
    (hφs : HasCompactSupport φ) (hφ : ContDiff ℝ 2 φ) (hφn : ∀ x, 0 ≤ φ x)
    (v : E) {R : ℝ} (hR : 0 < R)
    (hdisc : ∀ r ∈ Ioo 0 R, ∀ x ∈ Function.support φ, affineClosedDisc x v r ⊆ K) :
    (∫ x, f x * leviForm φ x v ∂μ) ≤ 0 :=
  hu.submean.integral_deficit_mul_leviForm_nonpos hKU C hC
    (hu.measurable_indicator_deficit hK hKU C) hD hf hfn hφs hφ hφn v hR hdisc

end SGPT.Foundations.Analysis
