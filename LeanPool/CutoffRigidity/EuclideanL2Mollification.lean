/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanL2Translations
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Actual Euclidean L² mollification

Normalized smooth compact Mathlib bumps, actual convolution, Jensen and the
proved translation estimate yield quantitative L² approximation.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Topology ContinuousLinearMap
open scoped ENNReal Convolution Pointwise

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual convolution with a normalized smooth compact bump. -/
@[expose] noncomputable def bumpMollification (φ : ContDiffBump (0 : E)) (f : E → ℝ) : E → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] f

/-- The actual normalized bump probability law, used for Jensen. -/
@[expose] noncomputable def bumpProbability (φ : ContDiffBump (0 : E)) : Measure E :=
  volume.withDensity (fun x => ENNReal.ofReal (φ.normed volume x))

instance bumpProbability_isProbabilityMeasure (φ : ContDiffBump (0 : E)) :
    IsProbabilityMeasure (bumpProbability φ) where
  measure_univ := by
    rw [bumpProbability, withDensity_apply _ MeasurableSet.univ]
    rw [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
      (Filter.Eventually.of_forall φ.nonneg_normed), φ.integral_normed]
    exact ENNReal.ofReal_one

/-- The actual bump probability is supported inside its prescribed radius. -/
theorem bumpProbability_ae_norm_le (φ : ContDiffBump (0 : E)) :
    ∀ᵐ y ∂bumpProbability φ, ‖y‖ ≤ φ.rOut := by
  apply (ae_withDensity_iff (φ.continuous_normed.measurable.ennreal_ofReal)).mpr
  filter_upwards with y hy
  have hpos : 0 < φ.normed volume y := (ENNReal.ofReal_ne_zero_iff).mp hy
  have hs : y ∈ Function.support (φ.normed volume) := ne_of_gt hpos
  rw [φ.support_normed_eq] at hs
  have hh : ‖y‖ < φ.rOut := by simpa only [Metric.mem_ball, dist_zero_right] using hs
  exact hh.le

/-- Integrating against the actual probability law gives precisely the
actual convolution, not an abstract smoothing operator. -/
theorem bumpProbability_integral_eq_convolution (φ : ContDiffBump (0 : E)) (f : E → ℝ) (x : E) :
    (∫ y, f (x - y) ∂bumpProbability φ) = bumpMollification φ f x := by
  rw [bumpProbability, integral_withDensity_eq_integral_toReal_smul
    φ.continuous_normed.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (φ.nonneg_normed _), smul_eq_mul,
    bumpMollification, convolution_lsmul]

/-- The smoothing is actually C∞ for every locally integrable input. -/
theorem bumpMollification_contDiff (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : LocallyIntegrable f volume) : ContDiff ℝ (↑(⊤ : ℕ∞)) (bumpMollification φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    φ.contDiff_normed hf

/-- Compact input gives actual compact smoothing support. -/
theorem bumpMollification_hasCompactSupport (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (bumpMollification φ f) :=
  φ.hasCompactSupport_normed.convolution (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) hf

/-- Actual smoothing error lies in Lebesgue L² for compact C¹ input. -/
theorem bumpMollification_error_memLp (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    MemLp (fun x => bumpMollification φ f x - f x) 2 volume := by
  have hc := (bumpMollification_contDiff φ hf.continuous.locallyIntegrable).continuous
  have hs := bumpMollification_hasCompactSupport φ hfc
  simpa only [Pi.sub_def] using (hc.memLp_of_hasCompactSupport hs).sub
    (hf.continuous.memLp_of_hasCompactSupport hfc : MemLp f 2 volume)

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
private theorem bumpMollification_error_of_translation_energy
    (φ : ContDiffBump (0 : E)) {f : E → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume)
    (C : ℝ) (hC : 0 ≤ C)
    (htrans : ∀ h : E, (∫ x, (f (x + h) - f x) ^ 2) ≤ C * ‖h‖ ^ 2) :
    MemLp (fun x => bumpMollification φ f x - f x) 2 volume ∧
      (∫ x, (bumpMollification φ f x - f x) ^ 2) ≤ φ.rOut ^ 2 * C := by
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
  have hinner : ∀ᵐ y ∂bumpProbability φ, (∫⁻ x, F x y) ≤ ENNReal.ofReal (φ.rOut ^ 2 * C) := by
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
    rw [mul_comm (φ.rOut ^ 2) C]
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg y) φ.rOut_pos.le).mpr hy) hC
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
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) hC)).mp hfinal

/-- Squared L² smoothing error from a translation bound with constant `C²`. -/
theorem bumpMollification_integral_error_of_translation_bound
    (φ : ContDiffBump (0 : E)) {f : E → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume)
    (C : ℝ) (htrans : ∀ h : E, (∫ x, (f (x + h) - f x) ^ 2) ≤ C ^ 2 * ‖h‖ ^ 2) :
    MemLp (fun x => bumpMollification φ f x - f x) 2 volume ∧
      (∫ x, (bumpMollification φ f x - f x) ^ 2) ≤ φ.rOut ^ 2 * C ^ 2 :=
  bumpMollification_error_of_translation_energy φ hfm hf (C ^ 2) (sq_nonneg C) htrans

/-- Genuine pointwise Jensen bound for the smoothing error. -/
theorem bumpMollification_error_sq_le (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : E) :
    (bumpMollification φ f x - f x) ^ 2 ≤
      ∫ y, (f (x - y) - f x) ^ 2 ∂bumpProbability φ :=
  bumpMollification_error_sq_le_of_memLp φ (hf.continuous.memLp_of_hasCompactSupport hfc) x

/-- Actual L² integrability under the compact bump probability. -/
theorem bumpProbability_difference_memLp (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (x : E) :
    MemLp (fun y => f (x - y) - f x) 2 (bumpProbability φ) := by
  have hm := bumpProbability_shift_memLp φ (hf.memLp_of_hasCompactSupport hfc) x
  simpa only [Pi.sub_def] using hm.sub (memLp_const (f x))

/-- Quantitative actual squared L² approximation by normalized smooth
compact convolution, with the actual support radius as constant. -/
theorem bumpMollification_error_integral_sq_le (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    (∫ x, (bumpMollification φ f x - f x) ^ 2) ≤
      φ.rOut ^ 2 * ∫ x, ‖gradient f x‖ ^ 2 := by
  have htrans (h : E) : (∫ x, (f (x + h) - f x) ^ 2) ≤ (∫ x, ‖gradient f x‖ ^ 2) * ‖h‖ ^ 2 := by
    simpa only [mul_comm] using c1_compact_translation_integral_sq_le hf hfc h
  exact (bumpMollification_error_of_translation_energy φ hf.continuous.measurable
    (hf.continuous.memLp_of_hasCompactSupport hfc) _ (integral_nonneg fun x => sq_nonneg _)
      htrans).2

/-- The quantitative genuine L² norm approximation. -/
theorem bumpMollification_error_L2_norm_le (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ‖(bumpMollification_error_memLp φ hf hfc).toLp (fun x => bumpMollification φ f x - f x)‖ ≤
      φ.rOut * ‖(c1_compact_gradient_memLp hf hfc).toLp (gradient f)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg φ.rOut_pos.le (norm_nonneg _))).mp
  rw [norm_toLp_sq (bumpMollification_error_memLp φ hf hfc), mul_pow, norm_toLp_norm_sq]
  exact bumpMollification_error_integral_sq_le φ hf hfc

/-- An actual smooth mollifier at positive scale ε, with exact outer radius ε. -/
@[expose] noncomputable def euclideanMollifierBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : E) :=
  ⟨ε / 2, ε, by positivity, by linarith⟩

/-- Scale ε gives approximation constant one in the actual L² norm. -/
theorem scaledMollification_error_L2_norm_le (ε : ℝ) (hε : 0 < ε) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ‖(bumpMollification_error_memLp (euclideanMollifierBump ε hε) hf hfc).toLp
      (fun x => bumpMollification (euclideanMollifierBump ε hε) f x - f x)‖ ≤
        ε * ‖(c1_compact_gradient_memLp hf hfc).toLp (gradient f)‖ :=
  bumpMollification_error_L2_norm_le (euclideanMollifierBump ε hε) hf hfc

/-- Genuine L² Cauchy bound for actual convolution with a continuous bilinear map. -/
theorem norm_convolution_le_toL2_norms
    {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    (L : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {k : E → F₁} {f : E → F₂}
    (hk : MemLp k 2 volume) (hf : MemLp f 2 volume) (x : E) :
    ‖(k ⋆[L, volume] f) x‖ ≤ ‖L‖ * ‖hk.toLp k‖ * ‖hf.toLp f‖ := by
  have hh := eNorm_convolution_le (p := 2) (q := 2) L hk.aestronglyMeasurable
    hf.aestronglyMeasurable x
  have hb : ‖L‖ₑ * eLpNorm k 2 volume * eLpNorm f 2 volume ≠ ⊤ := by finiteness
  have ht := ENNReal.toReal_mono hb hh
  simpa only [ENNReal.toReal_mul, toReal_eNorm, ← Lp.norm_toLp k hk, ← Lp.norm_toLp f hf] using ht

/-- The actual normalized smooth kernel is square integrable. -/
theorem bumpKernel_memLp (φ : ContDiffBump (0 : E)) : MemLp (φ.normed volume) 2 volume :=
  φ.continuous_normed.memLp_of_hasCompactSupport φ.hasCompactSupport_normed

/-- Its actual Fréchet derivative is square integrable, with compact support. -/
theorem bumpKernel_fderiv_memLp (φ : ContDiffBump (0 : E)) :
    MemLp (fderiv ℝ (φ.normed volume)) 2 volume := by
  have hc : Continuous (fderiv ℝ (φ.normed volume)) :=
    ((φ.contDiff_normed (n := 1)).fderiv_right (m := 0) (by norm_num)).continuous
  exact hc.memLp_of_hasCompactSupport (φ.hasCompactSupport_normed.fderiv ℝ)

/-- A fixed actual kernel gives a uniform global sup bound from the input L² norm. -/
theorem bumpMollification_sup_bound (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : MemLp f 2 volume) (x : E) :
    |bumpMollification φ f x| ≤
      (‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ * ‖(bumpKernel_memLp φ).toLp (φ.normed volume)‖) *
        ‖hf.toLp f‖ := by
  exact norm_convolution_le_toL2_norms (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) (bumpKernel_memLp φ) hf x

/-- Haar symmetry rewrites actual scalar convolution with the kernel shifted. -/
theorem scalar_convolution_eq_shifted_kernel (k f : E → ℝ) (x : E) :
    (k ⋆[lsmul ℝ ℝ, volume] f) x = ∫ y, k (x - y) * f y := by
  rw [convolution_lsmul]
  simp only [smul_eq_mul]
  rw [← integral_sub_left_eq_self (fun y => k y * f (x - y)) volume x]
  simp only [sub_sub_self]

/-- Kernel translations and genuine L² Cauchy--Schwarz give a Lipschitz
constant controlled by the kernel's actual gradient and the input's L² norm. -/
theorem convolution_lipschitzWith_of_C1_compact_kernel {k f : E → ℝ}
    (hk : ContDiff ℝ 1 k) (hkc : HasCompactSupport k) (hf : MemLp f 2 volume) :
    LipschitzWith (Real.toNNReal (‖(c1_compact_gradient_memLp hk hkc).toLp (gradient k)‖ * ‖hf.toLp
      f‖)) (k ⋆[lsmul ℝ ℝ, volume] f) := by
  have hkLp : MemLp k 2 volume := hk.continuous.memLp_of_hasCompactSupport hkc
  apply LipschitzWith.of_dist_le_mul
  intro x z
  let q (y : E) := k (y + (x - z)) - k y
  have hqLp : MemLp q 2 volume := c1_compact_translation_memLp hk hkc (x - z)
  let δ (y : E) := k (x - y) - k (z - y)
  have hδeq : δ = q ∘ (fun y : E => z - y) := by
    funext y
    dsimp [δ, q]
    congr 2
    abel
  have hδLp : MemLp δ 2 volume := by
    rw [hδeq]
    exact hqLp.comp_measurePreserving (volume.measurePreserving_sub_left z)
  have hδnorm : ‖hδLp.toLp δ‖ ≤ ‖x - z‖ * ‖(c1_compact_gradient_memLp hk hkc).toLp (gradient k)‖
    := by
    have heq : hδLp.toLp δ = Lp.compMeasurePreserving (fun y : E => z - y)
        (volume.measurePreserving_sub_left z) (hqLp.toLp q) := by
      apply Lp.ext
      filter_upwards [hδLp.coeFn_toLp,
        Lp.coeFn_compMeasurePreserving (hqLp.toLp q) (volume.measurePreserving_sub_left z),
        (volume.measurePreserving_sub_left z).quasiMeasurePreserving.ae (hqLp.coeFn_toLp)] with y
          hδ hcomp hq
      rw [hδ, hcomp]
      exact (congrFun hδeq y).trans hq.symm
    rw [heq, Lp.norm_compMeasurePreserving]
    exact c1_compact_translation_L2_norm_le hk hkc (x - z)
  have hprod (y : E) : Integrable (fun t => k (y - t) * f t) volume := by
    have hc := (ConvolutionExists.of_memLp_memLp (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) hkLp hf) y
    simpa only [lsmul_apply, smul_eq_mul] using hc.integrable_swap
  have hinner : (k ⋆[lsmul ℝ ℝ, volume] f) x - (k ⋆[lsmul ℝ ℝ, volume] f) z =
      inner ℝ (hδLp.toLp δ) (hf.toLp f) := by
    rw [scalar_convolution_eq_shifted_kernel, scalar_convolution_eq_shifted_kernel,
      real_inner_toLp, ← integral_sub (hprod x) (hprod z)]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [δ]
    ring
  rw [dist_eq_norm, hinner, Real.norm_eq_abs, dist_eq_norm]
  change |inner ℝ (hδLp.toLp δ) (hf.toLp f)| ≤
    max (‖(c1_compact_gradient_memLp hk hkc).toLp (gradient k)‖ * ‖hf.toLp f‖) 0 * ‖x - z‖
  rw [max_eq_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ ‖hδLp.toLp δ‖ * ‖hf.toLp f‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖x - z‖ * ‖(c1_compact_gradient_memLp hk hkc).toLp (gradient k)‖) * ‖hf.toLp f‖
      := by gcongr
    _ = _ := by ring

/-- The uniform global Lipschitz bound for actual normalized bump smoothings,
using only the input's actual L² norm. -/
theorem bumpMollification_lipschitzWith (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : MemLp f 2 volume) :
    LipschitzWith (Real.toNNReal (‖(c1_compact_gradient_memLp (φ.contDiff_normed (n
      := 1)) φ.hasCompactSupport_normed).toLp
      (gradient (φ.normed volume))‖ * ‖hf.toLp f‖)) (bumpMollification φ f) :=
  convolution_lipschitzWith_of_C1_compact_kernel (φ.contDiff_normed (n
    := 1)) φ.hasCompactSupport_normed hf

/-- A fixed smooth kernel gives a uniform actual Fréchet derivative bound
in terms of the actual input L² norm, as needed for Ascoli. -/
theorem bumpMollification_fderiv_bound (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : MemLp f 2 volume) (x : E) :
    ‖fderiv ℝ (bumpMollification φ f) x‖ ≤
      ‖(c1_compact_gradient_memLp (φ.contDiff_normed (n := 1)) φ.hasCompactSupport_normed).toLp
        (gradient (φ.normed volume))‖ * ‖hf.toLp f‖ := by
  have hh := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (bumpMollification_lipschitzWith φ hf)
  change ‖fderiv ℝ (bumpMollification φ f) x‖ ≤
    max (‖(c1_compact_gradient_memLp (φ.contDiff_normed (n := 1)) φ.hasCompactSupport_normed).toLp
      (gradient (φ.normed volume))‖ * ‖hf.toLp f‖) 0 at hh
  rwa [max_eq_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at hh

/-- Uniform smoothing bounds for every actual L²-bounded input family.
The kernel is fixed; neither C¹ regularity nor a common support of inputs
is needed for these sup and derivative bounds. -/
theorem bumpMollification_uniform_bounds (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : MemLp f 2 volume) (M : ℝ) (hM : ‖hf.toLp f‖ ≤ M) (x : E) :
    |bumpMollification φ f x| ≤
      (‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ * ‖(bumpKernel_memLp φ).toLp (φ.normed volume)‖) * M ∧
    ‖fderiv ℝ (bumpMollification φ f) x‖ ≤
      ‖(c1_compact_gradient_memLp (φ.contDiff_normed (n := 1)) φ.hasCompactSupport_normed).toLp
        (gradient (φ.normed volume))‖ * M := by
  constructor
  · exact (bumpMollification_sup_bound φ hf x).trans (by gcongr)
  · exact (bumpMollification_fderiv_bound φ hf x).trans (by gcongr)

end CutoffRigidity
