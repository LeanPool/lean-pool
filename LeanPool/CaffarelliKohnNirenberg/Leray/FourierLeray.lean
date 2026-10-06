/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierHeat
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Topology.Metrizable.Basic

/-!
# Fourier Leray

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform ComplexInnerProductSpace

noncomputable section
namespace CKN.Leray
open CKN.Foundation.Parabolic

/-- The real frequency vector represented in the complex velocity space of
`sec:regularised`. -/
@[expose]
def complexifyFrequency (ξ : L2Vec3) : ComplexVec3 :=
  WithLp.toLp 2 (fun i => (ξ i : ℂ))

/-- Complexification preserves the Euclidean magnitude of the frequency. -/
theorem complexifyFrequency_norm (ξ : L2Vec3) :
    ‖complexifyFrequency ξ‖ = ‖ξ‖ := by
  simp only [complexifyFrequency, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [Complex.norm_real, Real.norm_eq_abs]

/-- The reciprocal squared frequency magnitude, set to zero at the origin,
for the explicit Leray and pressure multiplier formulas. -/
@[expose]
def inverseFrequencyNormSq (ξ : L2Vec3) : ℝ :=
  if ξ = 0 then 0 else (‖ξ‖ ^ 2)⁻¹

/-- The Leray symbol in coordinates, written in a form suitable for pointwise
Fourier multiplication. -/
@[expose]
def lerayApplyFormula (ξ : L2Vec3) (z : ComplexVec3) : ComplexVec3 :=
  z - (((inverseFrequencyNormSq ξ : ℂ) *
    inner ℂ (complexifyFrequency ξ) z) • complexifyFrequency ξ)

/-- The coordinate formula for the Leray symbol is Borel measurable in
frequency and input, as required for its `L²` multiplier action. -/
theorem lerayApplyFormula_measurable :
    Measurable (fun p : L2Vec3 × ComplexVec3 =>
      lerayApplyFormula p.1 p.2) := by
  have heq : (fun p : L2Vec3 × ComplexVec3 =>
      lerayApplyFormula p.1 p.2) = fun p => if p.1 = 0 then p.2 else
        p.2 - ((((‖p.1‖ ^ 2)⁻¹ : ℝ) : ℂ) *
          inner ℂ (complexifyFrequency p.1) p.2) • complexifyFrequency p.1 := by
    funext p
    by_cases h : p.1 = 0
    · simp [lerayApplyFormula, inverseFrequencyNormSq, complexifyFrequency, h]
    · simp [lerayApplyFormula, inverseFrequencyNormSq, h]
  rw [heq]
  apply Measurable.ite (by measurability) measurable_snd
  fun_prop [complexifyFrequency]

/-- A measurable frequency symbol with a uniform fiber bound acts on spatial
`L²` by pointwise multiplication in Fourier space. -/
theorem measurableFourierMultiplier_memLp
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [MeasurableSpace G] [BorelSpace G] [TopologicalSpace.PseudoMetrizableSpace G]
    [SecondCountableTopology G] [OpensMeasurableSpace G]
    (m : L2Vec3 × F → G) (hm : Measurable m)
    (C : ℝ)
    (hbound : ∀ ξ x, ‖m (ξ, x)‖ ≤ C * ‖x‖)
    (f : Lp (α := L2Vec3) F 2) :
    MemLp (fun ξ : L2Vec3 => m (ξ, f ξ)) 2 volume := by
  let g : L2Vec3 → G := fun ξ => m (ξ, f ξ)
  have hpair : AEStronglyMeasurable (fun ξ : L2Vec3 => (ξ, f ξ)) volume :=
    measurable_id.aestronglyMeasurable.prodMk (Lp.memLp f).aestronglyMeasurable
  have hg : AEStronglyMeasurable g volume := by
    exact hm.aestronglyMeasurable.comp_aemeasurable hpair.aemeasurable
  have hmem : MemLp g 2 volume :=
    (Lp.memLp f).of_le_mul hg (Filter.Eventually.of_forall fun ξ => hbound ξ (f ξ))
  exact hmem

/-- A measurable frequency symbol with a uniform fiber bound acts on spatial
`L²` by pointwise multiplication in Fourier space. -/
@[expose]
noncomputable def measurableFourierMultiplier
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [MeasurableSpace G] [BorelSpace G] [TopologicalSpace.PseudoMetrizableSpace G]
    [SecondCountableTopology G] [OpensMeasurableSpace G]
    (m : L2Vec3 × F → G) (hm : Measurable m)
    (C : ℝ)
    (hbound : ∀ ξ x, ‖m (ξ, x)‖ ≤ C * ‖x‖)
    (f : Lp (α := L2Vec3) F 2) : Lp (α := L2Vec3) G 2 :=
  (measurableFourierMultiplier_memLp m hm C hbound f).toLp
    (fun ξ => m (ξ, f ξ))

/-- The `L²` multiplier agrees almost everywhere with its pointwise symbol
formula. -/
theorem measurableFourierMultiplier_ae_eq
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [MeasurableSpace G] [BorelSpace G] [TopologicalSpace.PseudoMetrizableSpace G]
    [SecondCountableTopology G] [OpensMeasurableSpace G]
    (m : L2Vec3 × F → G) (hm : Measurable m)
    (C : ℝ)
    (hbound : ∀ ξ x, ‖m (ξ, x)‖ ≤ C * ‖x‖)
    (f : Lp (α := L2Vec3) F 2) :
    (fun ξ => measurableFourierMultiplier m hm C hbound f ξ) =ᵐ[volume]
      (fun ξ => m (ξ, f ξ)) := by
  exact (measurableFourierMultiplier_memLp m hm C hbound f).coeFn_toLp

/-- A measurable Fourier multiplier has the same uniform fiber bound on its
`L²` operator norm. -/
theorem measurableFourierMultiplier_norm_le
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [MeasurableSpace G] [BorelSpace G] [TopologicalSpace.PseudoMetrizableSpace G]
    [SecondCountableTopology G] [OpensMeasurableSpace G]
    (m : L2Vec3 × F → G) (hm : Measurable m)
    (C : ℝ)
    (hbound : ∀ ξ x, ‖m (ξ, x)‖ ≤ C * ‖x‖)
    (f : Lp (α := L2Vec3) F 2) :
    ‖measurableFourierMultiplier m hm C hbound f‖ ≤ C * ‖f‖ := by
  let hmem := measurableFourierMultiplier_memLp m hm C hbound f
  change ‖hmem.toLp (fun ξ => m (ξ, f ξ))‖ ≤ C * ‖f‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hmem.coeFn_toLp] with ξ hξ
  rw [hξ]
  exact hbound ξ (f ξ)

/-- The complex line parallel to a frequency vector, used to define the
orthogonal Leray symbol in `sec:regularised`. -/
@[expose]
def lerayAxis (ξ : L2Vec3) : Submodule ℂ ComplexVec3 :=
  ℂ ∙ complexifyFrequency ξ

/-- The orthogonal projection onto the complement of the frequency direction,
with the identity value at zero, as in `sec:regularised`. -/
@[expose]
def leraySymbol (ξ : L2Vec3) : ComplexVec3 →L[ℂ] ComplexVec3 :=
  (lerayAxis ξ)ᗮ.starProjection

/-- The Leray symbol is an `L²`-fiber contraction, used in
`lem:reg-multiplier-bounds`. -/
theorem leraySymbol_norm_le (ξ : L2Vec3) (z : ComplexVec3) :
    ‖leraySymbol ξ z‖ ≤ ‖z‖ := by
  exact (lerayAxis ξ)ᗮ.norm_starProjection_apply_le z

/-- The orthogonal Leray symbol has the explicit coordinate formula used in
`sec:regularised`. -/
theorem leraySymbol_apply_eq_formula (ξ : L2Vec3) (z : ComplexVec3) :
    leraySymbol ξ z = lerayApplyFormula ξ z := by
  by_cases hξ : ξ = 0
  · subst ξ
    have hz : complexifyFrequency (0 : L2Vec3) = (0 : ComplexVec3) := by
      apply PiLp.ext
      intro i
      simp [complexifyFrequency]
    simp [leraySymbol, lerayAxis, lerayApplyFormula, inverseFrequencyNormSq,
      Submodule.starProjection_top, hz]
  · change ((ℂ ∙ complexifyFrequency ξ)ᗮ).starProjection z = _
    rw [Submodule.starProjection_orthogonal]
    simp only [sub_apply, ContinuousLinearMap.id_apply]
    rw [Submodule.starProjection_singleton]
    simp only [lerayApplyFormula, inverseFrequencyNormSq, hξ, ↓reduceIte]
    conv_lhs => rw [complexifyFrequency_norm]
    congr 1
    rw [div_eq_mul_inv, Complex.ofReal_inv]
    congr 1
    rw [mul_comm]
    rfl

/-- The Leray projection acting on frequency-space vector `L²`. -/
@[expose]
noncomputable def lerayFourierMultiplier
    (v : Lp (α := L2Vec3) ComplexVec3 2) :
    Lp (α := L2Vec3) ComplexVec3 2 :=
  measurableFourierMultiplier
    (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
    lerayApplyFormula_measurable 1
    (by
      intro ξ z
      rw [← leraySymbol_apply_eq_formula]
      simpa using leraySymbol_norm_le ξ z)
    v

/-- The Leray Fourier multiplier is an `L²` contraction. -/
theorem lerayFourierMultiplier_norm_le
    (v : Lp (α := L2Vec3) ComplexVec3 2) :
    ‖lerayFourierMultiplier v‖ ≤ ‖v‖ := by
  simpa [lerayFourierMultiplier] using measurableFourierMultiplier_norm_le
    (m := fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
    lerayApplyFormula_measurable 1
    (by
      intro ξ z
      rw [← leraySymbol_apply_eq_formula]
      simpa using leraySymbol_norm_le ξ z)
    v

/-- The physical Leray projection on complex velocity fields, obtained by
Fourier transformation, pointwise projection, and inverse transformation. -/
@[expose]
noncomputable def lerayProjectionL2
    (v : Lp (α := L2Vec3) ComplexVec3 2) :
    Lp (α := L2Vec3) ComplexVec3 2 := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  exact ℱ.symm (lerayFourierMultiplier (ℱ v))

/-- The physical Leray projection is an `L²` contraction. -/
theorem lerayProjectionL2_norm_le
    (v : Lp (α := L2Vec3) ComplexVec3 2) :
    ‖lerayProjectionL2 v‖ ≤ ‖v‖ := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  change ‖ℱ.symm (lerayFourierMultiplier (ℱ v))‖ ≤ ‖v‖
  rw [ℱ.symm.norm_map]
  calc
    ‖lerayFourierMultiplier (ℱ v)‖ ≤ ‖ℱ v‖ := lerayFourierMultiplier_norm_le _
    _ = ‖v‖ := ℱ.norm_map v

/-- The range of the Leray symbol is orthogonal to the frequency direction,
used to verify divergence freedom in `lem:reg-multiplier-bounds`. -/
theorem leraySymbol_divergence_free (ξ : L2Vec3) (z : ComplexVec3) :
    inner ℂ (complexifyFrequency ξ) (leraySymbol ξ z) = 0 := by
  have hz : leraySymbol ξ z ∈ (lerayAxis ξ)ᗮ :=
    Submodule.starProjection_apply_mem _ _
  have haxis : complexifyFrequency ξ ∈ lerayAxis ξ :=
    Submodule.mem_span_singleton_self (complexifyFrequency ξ)
  have hperp := (Submodule.mem_orthogonal' (K := lerayAxis ξ) (leraySymbol ξ z)).mp hz
    (complexifyFrequency ξ) haxis
  exact inner_eq_zero_symm.mp hperp

/-- The Leray Fourier projection has divergence-free range almost everywhere
in frequency space. -/
theorem lerayFourierMultiplier_divergence_free_ae
    (v : Lp (α := L2Vec3) ComplexVec3 2) :
    ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ) (lerayFourierMultiplier v ξ) = 0 := by
  filter_upwards [measurableFourierMultiplier_ae_eq
    (m := fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
    lerayApplyFormula_measurable 1
    (by
      intro ξ z
      rw [← leraySymbol_apply_eq_formula]
      simpa using leraySymbol_norm_le ξ z)
    v] with ξ hξ
  change inner ℂ (complexifyFrequency ξ)
    (measurableFourierMultiplier
      (fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
      lerayApplyFormula_measurable 1
      (by
        intro η z
        rw [← leraySymbol_apply_eq_formula]
        simpa using leraySymbol_norm_le η z)
      v ξ) = 0
  rw [hξ, ← leraySymbol_apply_eq_formula]
  exact leraySymbol_divergence_free ξ (v ξ)

/-- The Fourier symbol for tensor divergence, with the first tensor index
contracted against the frequency vector in `sec:regularised`. -/
@[expose]
def tensorDivergenceLinear (ξ : L2Vec3) : ComplexTensor3 →ₗ[ℂ] ComplexVec3 where
  toFun F := ∑ i : Fin 3, (ξ i : ℂ) • F i
  map_add' F G := by simp [Finset.sum_add_distrib, smul_add]
  map_smul' c F := by
    change (∑ i : Fin 3, (ξ i : ℂ) • (c • F i)) = c • ∑ i : Fin 3, (ξ i : ℂ) • F i
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul, smul_smul, mul_comm]

/-- Tensor divergence has fiber norm at most the frequency magnitude, used in
`lem:reg-multiplier-bounds`. -/
theorem tensorDivergence_norm_le (ξ : L2Vec3) (F : ComplexTensor3) :
    ‖tensorDivergenceLinear ξ F‖ ≤ ‖ξ‖ * ‖F‖ := by
  have htriangle :
      ‖tensorDivergenceLinear ξ F‖ ≤ ∑ i : Fin 3, |ξ i| * ‖F i‖ := by
    change ‖∑ i : Fin 3, (ξ i : ℂ) • F i‖ ≤ ∑ i : Fin 3, |ξ i| * ‖F i‖
    calc
      ‖∑ i : Fin 3, (ξ i : ℂ) • F i‖ ≤ ∑ i : Fin 3, ‖(ξ i : ℂ) • F i‖ := norm_sum_le _ _
      _ = ∑ i : Fin 3, |ξ i| * ‖F i‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [norm_smul, Real.norm_eq_abs]
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin 3 => |ξ i|) (fun i : Fin 3 => ‖F i‖)
  have hxi : ‖ξ‖ ^ 2 = ∑ i : Fin 3, |ξ i| ^ 2 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_sq_eq_of_L2 _ ξ)
  have hF : ‖F‖ ^ 2 = ∑ i : Fin 3, ‖F i‖ ^ 2 := by
    exact PiLp.norm_sq_eq_of_L2 _ F
  have hsq : (∑ i : Fin 3, |ξ i| * ‖F i‖) ^ 2 ≤ (‖ξ‖ * ‖F‖) ^ 2 := by
    rw [mul_pow, hxi, hF]
    exact hcauchy
  have hsum0 : 0 ≤ ∑ i : Fin 3, |ξ i| * ‖F i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hprod0 : 0 ≤ ‖ξ‖ * ‖F‖ := mul_nonneg (norm_nonneg ξ) (norm_nonneg F)
  have hsum : ∑ i : Fin 3, |ξ i| * ‖F i‖ ≤ ‖ξ‖ * ‖F‖ := by
    nlinarith only [hsq, hsum0, hprod0]
  exact htriangle.trans hsum


/-- The bounded continuous-linear-map form of the tensor-divergence symbol. -/
@[expose]
def tensorDivergenceCLM (ξ : L2Vec3) : ComplexTensor3 →L[ℂ] ComplexVec3 :=
  (tensorDivergenceLinear ξ).mkContinuous ‖ξ‖ (tensorDivergence_norm_le ξ)

/-- The double-Riesz pressure symbol, with value zero at zero frequency, as
in `sec:regularised`. -/
@[expose]
def pressureFrequencySymbol (ξ : L2Vec3) : ComplexTensor3 →L[ℂ] ℂ :=
  if ξ = 0 then 0 else
    (-(((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) •
      (innerSL ℂ (complexifyFrequency ξ)).comp (tensorDivergenceCLM ξ)

/-- The pressure symbol is an `L²`-fiber contraction, hence satisfies the
weaker bound stated in `lem:reg-multiplier-bounds`. -/
theorem pressureFrequencySymbol_norm_le (ξ : L2Vec3) :
    ‖pressureFrequencySymbol ξ‖ ≤ 1 := by
  rw [pressureFrequencySymbol]
  split_ifs with hξ
  · simp
  · have hξnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hinner : ‖innerSL ℂ (complexifyFrequency ξ)‖ = ‖ξ‖ := by
      rw [innerSL_apply_norm, complexifyFrequency_norm]
    have hdiv : ‖tensorDivergenceCLM ξ‖ ≤ ‖ξ‖ := by
      exact LinearMap.mkContinuous_norm_le (tensorDivergenceLinear ξ)
        (norm_nonneg _) (fun F => tensorDivergence_norm_le ξ F)
    have hcomp :
        ‖(innerSL ℂ (complexifyFrequency ξ)).comp (tensorDivergenceCLM ξ)‖ ≤
          ‖ξ‖ * ‖ξ‖ := by
      calc
        ‖(innerSL ℂ (complexifyFrequency ξ)).comp (tensorDivergenceCLM ξ)‖ ≤
            ‖innerSL ℂ (complexifyFrequency ξ)‖ * ‖tensorDivergenceCLM ξ‖ :=
          (innerSL ℂ (complexifyFrequency ξ)).opNorm_comp_le (tensorDivergenceCLM ξ)
        _ ≤ ‖ξ‖ * ‖ξ‖ := by rw [hinner]; gcongr
    calc
      ‖-(((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) •
          (innerSL ℂ (complexifyFrequency ξ)).comp (tensorDivergenceCLM ξ)‖
          = ‖-(((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)‖ *
            ‖(innerSL ℂ (complexifyFrequency ξ)).comp (tensorDivergenceCLM ξ)‖ := norm_smul _ _
      _ ≤ (‖ξ‖ ^ 2)⁻¹ * (‖ξ‖ * ‖ξ‖) := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : 0 < (‖ξ‖ ^ 2)⁻¹)]
        exact mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ = 1 := by field_simp [ne_of_gt hξnorm]

/-- The pressure multiplier evaluated on one tensor, with the value zero
assigned at zero frequency. -/
@[expose]
def pressureApplyFormula (ξ : L2Vec3) (F : ComplexTensor3) : ℂ :=
  if ξ = 0 then 0 else
    -(((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      inner ℂ (complexifyFrequency ξ) (tensorDivergenceLinear ξ F)

/-- Evaluation of the pressure symbol agrees with its coordinate formula. -/
theorem pressureFrequencySymbol_apply_eq_formula (ξ : L2Vec3) (F : ComplexTensor3) :
    pressureFrequencySymbol ξ F = pressureApplyFormula ξ F := by
  unfold pressureFrequencySymbol pressureApplyFormula
  by_cases hξ : ξ = 0
  · simp [hξ]
  · simp only [hξ, ↓reduceIte, smul_apply,
      ContinuousLinearMap.comp_apply]
    rfl

/-- The pressure multiplier formula is measurable in frequency and tensor. -/
theorem pressureApplyFormula_measurable :
    Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      pressureApplyFormula p.1 p.2) := by
  have hdiv : Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      tensorDivergenceLinear p.1 p.2) := by
    change Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      ∑ i : Fin 3, (p.1 i : ℂ) • p.2 i)
    fun_prop
  have hfreq : Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      complexifyFrequency p.1) := by
    fun_prop [complexifyFrequency]
  have hinter : Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      inner ℂ (complexifyFrequency p.1) (tensorDivergenceLinear p.1 p.2)) :=
    continuous_inner.measurable.comp (hfreq.prodMk hdiv)
  have hcoef : Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      -(((‖p.1‖ ^ 2)⁻¹ : ℝ) : ℂ)) := by
    fun_prop
  change Measurable (fun p : L2Vec3 × ComplexTensor3 =>
    if p.1 = 0 then 0 else
      (-(((‖p.1‖ ^ 2)⁻¹ : ℝ) : ℂ)) *
        inner ℂ (complexifyFrequency p.1) (tensorDivergenceLinear p.1 p.2))
  apply Measurable.ite (by measurability) measurable_const
  exact hcoef.mul hinter

/-- The pressure multiplier formula is pointwise bounded by the Frobenius
norm of its tensor input. -/
theorem pressureApplyFormula_norm_le (ξ : L2Vec3) (F : ComplexTensor3) :
    ‖pressureApplyFormula ξ F‖ ≤ ‖F‖ := by
  rw [← pressureFrequencySymbol_apply_eq_formula]
  calc
    ‖pressureFrequencySymbol ξ F‖ ≤ ‖pressureFrequencySymbol ξ‖ * ‖F‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖F‖ := by
      exact mul_le_mul_of_nonneg_right (pressureFrequencySymbol_norm_le ξ) (norm_nonneg _)
    _ = ‖F‖ := by ring

/-- The pressure Fourier multiplier maps tensor `L²` into scalar `L²`. -/
@[expose]
noncomputable def pressureFourierMultiplier
    (F : Lp (α := L2Vec3) ComplexTensor3 2) :
    Lp (α := L2Vec3) ℂ 2 :=
  measurableFourierMultiplier
    (fun p : L2Vec3 × ComplexTensor3 => pressureApplyFormula p.1 p.2)
    pressureApplyFormula_measurable 1
    (by
      intro ξ T
      simpa using pressureApplyFormula_norm_le ξ T)
    F

/-- The pressure Fourier multiplier is bounded on `L²` by one, hence by the
constant three in `lem:reg-multiplier-bounds`. -/
theorem pressureFourierMultiplier_norm_le
    (F : Lp (α := L2Vec3) ComplexTensor3 2) :
    ‖pressureFourierMultiplier F‖ ≤ ‖F‖ := by
  simpa [pressureFourierMultiplier] using
    measurableFourierMultiplier_norm_le
      (m := fun p : L2Vec3 × ComplexTensor3 => pressureApplyFormula p.1 p.2)
      pressureApplyFormula_measurable 1
      (by intro ξ T; simpa using pressureApplyFormula_norm_le ξ T) F

/-- The physical double-Riesz pressure map on tensor-valued `L²`. -/
@[expose]
noncomputable def pressureL2Operator
    (F : Lp (α := L2Vec3) ComplexTensor3 2) :
    Lp (α := L2Vec3) ℂ 2 := by
  let ℱT := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  let ℱS := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ℂ
  exact ℱS.symm (pressureFourierMultiplier (ℱT F))

/-- The physical double-Riesz pressure map has the stronger `L²` bound one. -/
theorem pressureL2Operator_norm_le
    (F : Lp (α := L2Vec3) ComplexTensor3 2) :
    ‖pressureL2Operator F‖ ≤ ‖F‖ := by
  let ℱT := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  let ℱS := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ℂ
  change ‖ℱS.symm (pressureFourierMultiplier (ℱT F))‖ ≤ ‖F‖
  rw [ℱS.symm.norm_map]
  calc
    ‖pressureFourierMultiplier (ℱT F)‖ ≤ ‖ℱT F‖ := pressureFourierMultiplier_norm_le _
    _ = ‖F‖ := ℱT.norm_map F

/-- The pointwise Fourier symbol of the heat-regularized Leray-Stokes map in
`sec:regularised`. -/
@[expose]
def stokesFrequencySymbol (t : ℝ) (ξ : L2Vec3) :
    ComplexTensor3 →L[ℂ] ComplexVec3 :=
  (heatSymbol t ξ * (2 * Real.pi * Complex.I : ℂ)) •
    ((leraySymbol ξ).comp (tensorDivergenceCLM ξ))

/-- The Stokes symbol is bounded by the heat-gradient multiplier times the
Frobenius norm of the input tensor. -/
theorem stokesFrequencySymbol_apply_norm_le (t : ℝ) (ξ : L2Vec3)
    (F : ComplexTensor3) :
    ‖stokesFrequencySymbol t ξ F‖ ≤
      (2 * Real.pi * ‖ξ‖ * Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) * ‖F‖ := by
  rw [stokesFrequencySymbol, smul_apply]
  calc
    ‖(heatSymbol t ξ * (2 * Real.pi * Complex.I : ℂ)) •
        ((leraySymbol ξ).comp (tensorDivergenceCLM ξ) F)‖
        ≤ ‖heatSymbol t ξ * (2 * Real.pi * Complex.I : ℂ)‖ *
          ‖(leraySymbol ξ).comp (tensorDivergenceCLM ξ) F‖ := norm_smul_le _ _
    _ ≤ ‖heatSymbol t ξ * (2 * Real.pi * Complex.I : ℂ)‖ *
          ‖tensorDivergenceCLM ξ F‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact leraySymbol_norm_le ξ _
    _ ≤ ‖heatSymbol t ξ * (2 * Real.pi * Complex.I : ℂ)‖ * (‖ξ‖ * ‖F‖) := by
      gcongr
      exact tensorDivergence_norm_le ξ F
    _ = (2 * Real.pi * ‖ξ‖ * Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) * ‖F‖ := by
      rw [heatSymbol, Complex.norm_mul, Complex.ofReal_exp, Complex.norm_exp_ofReal]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring

/-- The Gaussian times frequency has supremum `(2 e t)^{-1/2}`, as needed in
`lem:reg-multiplier-bounds`. -/
theorem heatGradient_symbol_bound {t : ℝ} (ht : 0 < t) (ξ : L2Vec3) :
    2 * Real.pi * ‖ξ‖ * Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2) ≤
      1 / Real.sqrt (2 * Real.exp 1 * t) := by
  let y : ℝ := 8 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2
  have hy : 0 ≤ y := by
    dsimp [y]
    positivity
  have h := Real.mul_exp_neg_le_exp_neg_one y
  have hdivide : y * Real.exp (-y) / (2 * t) ≤ Real.exp (-1) / (2 * t) :=
    div_le_div_of_nonneg_right h (by positivity)
  have hsq :
      (2 * Real.pi * ‖ξ‖ * Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) ^ 2 ≤
      (1 / Real.sqrt (2 * Real.exp 1 * t)) ^ 2 := by
    calc
      (2 * Real.pi * ‖ξ‖ * Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) ^ 2 =
          y * Real.exp (-y) / (2 * t) := by
        have hexp : Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2) ^ 2 =
            Real.exp (-(8 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) := by
          rw [pow_two, ← Real.exp_add]
          congr 1; ring
        rw [mul_pow, hexp]
        dsimp [y]
        field_simp
        ring
      _ ≤ Real.exp (-1) / (2 * t) := hdivide
      _ = (1 / Real.sqrt (2 * Real.exp 1 * t)) ^ 2 := by
        rw [Real.exp_neg, one_div, inv_pow, Real.sq_sqrt]
        · ring
        · positivity
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  exact hsq

/-- The Leray-regularized Stokes symbol has the Abel-kernel bound in
`lem:reg-multiplier-bounds`. -/
theorem stokesFrequencySymbol_norm_le {t : ℝ} (ht : 0 < t) (ξ : L2Vec3) :
    ‖stokesFrequencySymbol t ξ‖ ≤ 1 / Real.sqrt (2 * Real.exp 1 * t) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro F
  calc
    ‖stokesFrequencySymbol t ξ F‖ ≤
        (2 * Real.pi * ‖ξ‖ * Real.exp (-4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) * ‖F‖ :=
      stokesFrequencySymbol_apply_norm_le t ξ F
    _ ≤ (1 / Real.sqrt (2 * Real.exp 1 * t)) * ‖F‖ := by
      gcongr
      exact heatGradient_symbol_bound ht ξ

/-- The pointwise heat, tensor-divergence, and Leray formula for the Stokes
multiplier in `sec:regularised`. -/
@[expose]
def stokesApplyFormula (t : ℝ) (ξ : L2Vec3) (F : ComplexTensor3) : ComplexVec3 :=
  (heatSymbol t ξ * (2 * Real.pi * Complex.I : ℂ)) •
    lerayApplyFormula ξ (tensorDivergenceLinear ξ F)

/-- Evaluation of the Stokes symbol agrees with its coordinate formula. -/
theorem stokesFrequencySymbol_apply_eq_formula (t : ℝ) (ξ : L2Vec3)
    (F : ComplexTensor3) :
    stokesFrequencySymbol t ξ F = stokesApplyFormula t ξ F := by
  simp [stokesFrequencySymbol, stokesApplyFormula, smul_apply,
    ContinuousLinearMap.comp_apply, leraySymbol_apply_eq_formula,
    tensorDivergenceCLM]

/-- The Leray--Stokes symbol has divergence-free range at each frequency. -/
theorem stokesFrequencySymbol_divergence_free (t : ℝ) (ξ : L2Vec3)
    (F : ComplexTensor3) :
    inner ℂ (complexifyFrequency ξ) (stokesFrequencySymbol t ξ F) = 0 := by
  rw [stokesFrequencySymbol, smul_apply, ContinuousLinearMap.comp_apply,
    inner_smul_right, leraySymbol_divergence_free]
  simp

/-- The Stokes multiplier formula is measurable in frequency and tensor. -/
theorem stokesApplyFormula_measurable (t : ℝ) :
    Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      stokesApplyFormula t p.1 p.2) := by
  have hdiv : Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      tensorDivergenceLinear p.1 p.2) := by
    change Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      ∑ i : Fin 3, (p.1 i : ℂ) • p.2 i)
    fun_prop
  have hpair : Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      (p.1, tensorDivergenceLinear p.1 p.2)) :=
    measurable_fst.prodMk hdiv
  have hproject : Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      lerayApplyFormula p.1 (tensorDivergenceLinear p.1 p.2)) :=
    lerayApplyFormula_measurable.comp hpair
  have hheat : Measurable (fun p : L2Vec3 × ComplexTensor3 =>
      heatSymbol t p.1 * (2 * Real.pi * Complex.I : ℂ)) := by
    fun_prop [heatSymbol]
  change Measurable (fun p : L2Vec3 × ComplexTensor3 =>
    (heatSymbol t p.1 * (2 * Real.pi * Complex.I : ℂ)) •
      lerayApplyFormula p.1 (tensorDivergenceLinear p.1 p.2))
  exact continuous_smul.measurable.comp (hheat.prodMk hproject)

/-- The Stokes multiplier formula has the integrable Abel-kernel fiber bound
from `lem:reg-multiplier-bounds`. -/
theorem stokesApplyFormula_norm_le {t : ℝ} (ht : 0 < t) (ξ : L2Vec3)
    (F : ComplexTensor3) :
    ‖stokesApplyFormula t ξ F‖ ≤
      (1 / Real.sqrt (2 * Real.exp 1 * t)) * ‖F‖ := by
  rw [← stokesFrequencySymbol_apply_eq_formula]
  calc
    ‖stokesFrequencySymbol t ξ F‖ ≤ ‖stokesFrequencySymbol t ξ‖ * ‖F‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (1 / Real.sqrt (2 * Real.exp 1 * t)) * ‖F‖ := by
      exact mul_le_mul_of_nonneg_right (stokesFrequencySymbol_norm_le ht ξ)
        (norm_nonneg _)

/-- The Stokes Fourier multiplier on tensor-valued spatial `L²`. -/
@[expose]
noncomputable def stokesFourierMultiplier {t : ℝ} (ht : 0 < t)
    (F : Lp (α := L2Vec3) ComplexTensor3 2) :
    Lp (α := L2Vec3) ComplexVec3 2 :=
  measurableFourierMultiplier
    (fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
    (stokesApplyFormula_measurable t)
    (1 / Real.sqrt (2 * Real.exp 1 * t))
    (by intro ξ T; exact stokesApplyFormula_norm_le ht ξ T)
    F

/-- The Stokes Fourier multiplier has the `t^{-1/2}` bound in
`lem:reg-multiplier-bounds`. -/
theorem stokesFourierMultiplier_norm_le {t : ℝ} (ht : 0 < t)
    (F : Lp (α := L2Vec3) ComplexTensor3 2) :
    ‖stokesFourierMultiplier ht F‖ ≤
      (1 / Real.sqrt (2 * Real.exp 1 * t)) * ‖F‖ := by
  simpa [stokesFourierMultiplier] using
    measurableFourierMultiplier_norm_le
      (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
      (stokesApplyFormula_measurable t)
      (1 / Real.sqrt (2 * Real.exp 1 * t))
      (by intro ξ T; exact stokesApplyFormula_norm_le ht ξ T) F

/-- The Stokes Fourier multiplier has divergence-free range almost everywhere
in frequency space. -/
theorem stokesFourierMultiplier_divergence_free_ae {t : ℝ} (ht : 0 < t)
    (F : Lp (α := L2Vec3) ComplexTensor3 2) :
    ∀ᵐ ξ ∂volume,
      inner ℂ (complexifyFrequency ξ) (stokesFourierMultiplier ht F ξ) = 0 := by
  filter_upwards [measurableFourierMultiplier_ae_eq
    (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
    (stokesApplyFormula_measurable t)
    (1 / Real.sqrt (2 * Real.exp 1 * t))
    (by intro ξ T; exact stokesApplyFormula_norm_le ht ξ T)
    F] with ξ hξ
  change inner ℂ (complexifyFrequency ξ)
    (measurableFourierMultiplier
      (fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula t p.1 p.2)
      (stokesApplyFormula_measurable t)
      (1 / Real.sqrt (2 * Real.exp 1 * t))
      (by intro η T; exact stokesApplyFormula_norm_le ht η T)
      F ξ) = 0
  rw [hξ, ← stokesFrequencySymbol_apply_eq_formula]
  exact stokesFrequencySymbol_divergence_free t ξ (F ξ)

/-- The physical heat-regularized Leray-Stokes operator on tensor-valued
spatial `L²`. -/
@[expose]
noncomputable def stokesL2Operator {t : ℝ} (ht : 0 < t)
    (F : Lp (α := L2Vec3) ComplexTensor3 2) :
    Lp (α := L2Vec3) ComplexVec3 2 := by
  let ℱT := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  let ℱV := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  exact ℱV.symm (stokesFourierMultiplier ht (ℱT F))

/-- The physical Stokes operator has the integrable `t^{-1/2}` bound. -/
theorem stokesL2Operator_norm_le {t : ℝ} (ht : 0 < t)
    (F : Lp (α := L2Vec3) ComplexTensor3 2) :
    ‖stokesL2Operator ht F‖ ≤
      (1 / Real.sqrt (2 * Real.exp 1 * t)) * ‖F‖ := by
  let ℱT := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  let ℱV := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  change ‖ℱV.symm (stokesFourierMultiplier ht (ℱT F))‖ ≤ _
  rw [ℱV.symm.norm_map]
  calc
    ‖stokesFourierMultiplier ht (ℱT F)‖ ≤
        (1 / Real.sqrt (2 * Real.exp 1 * t)) * ‖ℱT F‖ :=
      stokesFourierMultiplier_norm_le ht _
    _ = (1 / Real.sqrt (2 * Real.exp 1 * t)) * ‖F‖ := by rw [ℱT.norm_map]

end CKN.Leray
