/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanL2Mollification

/-! # Quantitative actual mollification from a derived L² translation modulus

This extends the preceding C¹ argument to measurable actual L² inputs.
The hypothesis is a genuine translation estimate, not an approximation or
compactness assumption. Normalized smooth kernels have bounded density,
which proves all pointwise Jensen integrability conditions.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Topology ContinuousLinearMap
open scoped ENNReal Convolution Pointwise

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual smooth compact probability density is bounded above by a
finite multiple of Lebesgue measure. -/
theorem bumpProbability_le_smul_volume (φ : ContDiffBump (0 : E)) :
    ∃ M : ℝ, 0 ≤ M ∧ bumpProbability φ ≤ ENNReal.ofReal M • volume := by
  obtain ⟨M₀, hM₀⟩ := (φ.hasCompactSupport_normed (μ := (volume : Measure
    E))).exists_bound_of_continuousOn
    (φ.continuous_normed (μ := (volume : Measure E))).continuousOn
  let M := max M₀ 0
  have hM (y : E) : φ.normed volume y ≤ M := by
    have hn : ‖φ.normed volume y‖ ≤ M := by
      by_cases hy : y ∈ tsupport (φ.normed volume)
      · exact (hM₀ y hy).trans (le_max_left _ _)
      · have hz : φ.normed volume y = 0 := image_eq_zero_of_notMem_tsupport hy
        simpa only [hz, norm_zero] using le_max_right M₀ 0
    simpa only [Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed y)] using hn
  refine ⟨M, le_max_right _ _, ?_⟩
  rw [bumpProbability, ← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun y => ENNReal.ofReal_le_ofReal (hM y))

/-- Every actual Lebesgue L² input is pointwise square integrable under the
shifted bump probability; bounded kernel density proves this. -/
theorem bumpProbability_shift_memLp (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : MemLp f 2 volume) (x : E) :
    MemLp (fun y => f (x - y)) 2 (bumpProbability φ) := by
  obtain ⟨M, hM, hle⟩ := bumpProbability_le_smul_volume φ
  have ht : MemLp (fun y => f (x - y)) 2 volume :=
    hf.comp_measurePreserving (volume.measurePreserving_sub_left x)
  exact MemLp.mono_measure hle (ht.smul_measure ENNReal.ofReal_ne_top)

/-- Genuine Jensen for arbitrary actual Lebesgue L² input. -/
theorem bumpMollification_error_sq_le_of_memLp (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : MemLp f 2 volume) (x : E) :
    (bumpMollification φ f x - f x) ^ 2 ≤ ∫ y, (f (x - y) - f x) ^ 2 ∂bumpProbability φ := by
  have hm := bumpProbability_shift_memLp φ hf x
  have hg : MemLp (fun y => f (x - y) - f x) 2 (bumpProbability φ) := by
    simpa only [Pi.sub_def] using hm.sub (memLp_const (f x))
  have hj := variance_nonneg (fun y => f (x - y) - f x) (bumpProbability φ)
  rw [variance_eq_sub hg, integral_sub (hm.integrable (by norm_num)) (integrable_const _),
    bumpProbability_integral_eq_convolution, integral_const] at hj
  simp only [Pi.pow_apply, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hj
  linarith

/-- Actual quantitative L² smoothing approximation from an actual uniform
translation modulus. All error integrability is derived. -/
theorem bumpMollification_integral_error_of_translation_bound
    (φ : ContDiffBump (0 : E)) {f : E → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume)
    (C : ℝ) (_hC : 0 ≤ C)
    (htrans : ∀ h : E, (∫ x, (f (x + h) - f x) ^ 2) ≤ C ^ 2 * ‖h‖ ^ 2) :
    MemLp (fun x => bumpMollification φ f x - f x) 2 volume ∧
      (∫ x, (bumpMollification φ f x - f x) ^ 2) ≤ φ.rOut ^ 2 * C ^ 2 := by
  let F (x y : E) : ℝ≥0∞ := ENNReal.ofReal ((f (x - y) - f x) ^ 2)
  have hFm : Measurable (Function.uncurry F) :=
    (((hfm.comp (measurable_fst.sub measurable_snd)).sub (hfm.comp measurable_fst)).pow_const
      2).ennreal_ofReal
  have hpoint (x : E) : ENNReal.ofReal ((bumpMollification φ f x - f x) ^ 2) ≤
      ∫⁻ y, F x y ∂bumpProbability φ := by
    have hm := bumpProbability_shift_memLp φ hf x
    have hg : MemLp (fun y => f (x - y) - f x) 2 (bumpProbability φ) := by
      simpa only [Pi.sub_def] using hm.sub (memLp_const (f x))
    have hi := ENNReal.ofReal_le_ofReal (bumpMollification_error_sq_le_of_memLp φ hf x)
    rw [ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
      (Filter.Eventually.of_forall fun y => sq_nonneg _)] at hi
    exact hi
  have hi := lintegral_mono (μ := (volume : Measure E)) hpoint
  rw [lintegral_lintegral_swap hFm.aemeasurable] at hi
  have hinner : ∀ᵐ y ∂bumpProbability φ, (∫⁻ x, F x y) ≤ ENNReal.ofReal (φ.rOut ^ 2 * C ^ 2) := by
    filter_upwards [bumpProbability_ae_norm_le φ] with y hy
    have hdiff : MemLp (fun x => f (x - y) - f x) 2 volume := by
      simpa only [Function.comp_def, sub_eq_add_neg, Pi.sub_def, Pi.add_def, Pi.neg_def] using
        (hf.comp_measurePreserving (measurePreserving_add_right volume (-y))).sub hf
    change (∫⁻ x, ENNReal.ofReal ((f (x - y) - f x) ^ 2)) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hdiff.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have ht := htrans (-y)
    simp only [← sub_eq_add_neg, norm_neg] at ht
    apply ht.trans
    nlinarith [sq_le_sq₀ (norm_nonneg y) φ.rOut_pos.le |>.mpr hy, sq_nonneg C]
  have hb := lintegral_mono_ae hinner
  simp only [lintegral_const, measure_univ, mul_one] at hb
  have hfinal := hi.trans hb
  have hfloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have herrorM : AEStronglyMeasurable (fun x => bumpMollification φ f x - f x) volume :=
    ((bumpMollification_contDiff φ hfloc).continuous.measurable.sub hfm).aestronglyMeasurable
  have herrorInt : Integrable (fun x => (bumpMollification φ f x - f x) ^ 2) volume := by
    refine ⟨herrorM.pow 2, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)).2
    exact lt_of_le_of_lt hfinal ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq herrorM).mpr herrorInt, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal herrorInt
    (Filter.Eventually.of_forall fun x => sq_nonneg _)] at hfinal
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (sq_nonneg _))).mp hfinal

/-- Actual smoothing L² membership follows from the proved translation-modulus
error bound, without assuming an approximation property. -/
theorem bumpMollification_memLp_of_translation_bound
    (φ : ContDiffBump (0 : E)) {f : E → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume)
    (C : ℝ) (hC : 0 ≤ C)
    (htrans : ∀ h : E, (∫ x, (f (x + h) - f x) ^ 2) ≤ C ^ 2 * ‖h‖ ^ 2) :
    MemLp (bumpMollification φ f) 2 volume := by
  have he := (bumpMollification_integral_error_of_translation_bound φ hfm hf C hC htrans).1
  convert he.add hf using 1
  funext x
  simp

/-- The actual L² distance between smoothing and input is controlled by the
derived translation modulus. This is the uniform-approximation input for Ascoli. -/
theorem bumpMollification_L2_dist_le_of_translation_bound
    (φ : ContDiffBump (0 : E)) {f : E → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume)
    (C : ℝ) (hC : 0 ≤ C)
    (htrans : ∀ h : E, (∫ x, (f (x + h) - f x) ^ 2) ≤ C ^ 2 * ‖h‖ ^ 2) :
    ‖(bumpMollification_memLp_of_translation_bound φ hfm hf C hC htrans).toLp (bumpMollification φ
      f) -
      hf.toLp f‖ ≤ φ.rOut * C := by
  have hnorm : ‖(bumpMollification_memLp_of_translation_bound φ hfm hf C hC htrans).toLp
    (bumpMollification φ f) -
      hf.toLp f‖ ^ 2 = ∫ x, (bumpMollification φ f x - f x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub
      ((bumpMollification_memLp_of_translation_bound φ hfm hf C hC htrans).toLp (bumpMollification
        φ f))
      (hf.toLp f), (bumpMollification_memLp_of_translation_bound φ hfm hf C hC htrans).coeFn_toLp,
      hf.coeFn_toLp] with x hsub hsm hf'
    rw [hsub, Pi.sub_apply, hsm, hf', Real.inner_apply, pow_two]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg φ.rOut_pos.le hC)).mp
  rw [hnorm, mul_pow]
  exact (bumpMollification_integral_error_of_translation_bound φ hfm hf C hC htrans).2

/-- Common compact support of inputs gives common enlarged compact support
of the actual smoothing family. -/
theorem bumpMollification_eq_zero_off_add_support (φ : ContDiffBump (0 : E))
    {f : E → ℝ} {K : Set E} (hsupp : ∀ x ∉ K, f x = 0)
    (x : E) (hx : x ∉ Metric.closedBall (0 : E) φ.rOut + K) :
    bumpMollification φ f x = 0 := by
  by_contra hne
  have hs : x ∈ Function.support (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) := hne
  have hsub := support_convolution_subset (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    (f := φ.normed volume) (g := f) (μ := (volume : Measure E))
  obtain ⟨y, hy, z, hz, hyz⟩ := hsub hs
  apply hx
  refine ⟨y, ?_, z, ?_, hyz⟩
  · have hy' : y ∈ tsupport (φ.normed volume) := subset_tsupport _ hy
    rwa [φ.tsupport_normed_eq] at hy'
  · by_contra hzK
    exact hz (hsupp z hzK)

end CutoffRigidity
