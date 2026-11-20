/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Affine
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Measure.Support

/-! # Pushforwards by translations and linear equivalences

The law is pushed forward in the direction of the underlying map. Covariance and moment
identities are statements about that probability law. L² pullbacks are in `L2.Transport`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace
open scoped ENNReal

namespace FunctionalInequalities

universe u v

section TiltTransport

section MeasurableSpace

variable {A B : Type*}
  [MeasurableSpace A] [MeasurableSpace B]

/-- An indicator-density image law constrains the map almost everywhere for the base measure. -/
theorem Probability.ae_mem_of_map_tilted_eq_withDensity_indicator
    (μ : Measure A) (ν : Measure B) {φ : A → ℝ}
    (hint : Integrable (fun x => Real.exp (φ x)) μ)
    {f : A → B} (hf : AEMeasurable f (μ.tilted φ)) {S : Set B} (hS : MeasurableSet S)
    {w : B → ℝ≥0∞} (hw : Measurable w)
    (hmap : (μ.tilted φ).map f = ν.withDensity (S.indicator w)) :
    ∀ᵐ x ∂μ, f x ∈ S := by
  have hs : ∀ᵐ y ∂ν.withDensity (S.indicator w), y ∈ S := by
    apply (ae_withDensity_iff (hw.indicator hS)).2
    exact Filter.Eventually.of_forall fun y hy => by
      by_contra h
      exact hy (Set.indicator_of_notMem h _)
  have ht : ∀ᵐ x ∂μ.tilted φ, f x ∈ S := by
    apply ae_of_ae_map hf
    rw [hmap]
    exact hs
  exact (absolutelyContinuous_tilted hint).ae_le ht

/--
Pushing a density through a measurable equivalence: the new density is the old one composed with
the inverse. -/
theorem Probability.map_withDensity_measurableEquiv (e : A ≃ᵐ B) (μ : Measure A)
    (w : A → ENNReal) (hw : Measurable w) :
    (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ e.measurable,
    lintegral_withDensity_eq_lintegral_mul μ hw
      (show Measurable (fun x => φ (e x)) from hφ.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul (μ.map e)
      (show Measurable (fun y => w (e.symm y)) from hw.comp e.symm.measurable) hφ]
  simp only [Pi.mul_apply]
  rw [lintegral_map
      (show Measurable (fun y => w (e.symm y) * φ y) from (hw.comp e.symm.measurable).mul hφ)
      e.measurable]
  simp only [e.symm_apply_apply]

/--
The tilted measure transported through a measurable equivalence is the tilt of the image measure by
the composed weight. -/
theorem Probability.map_tilted_measurableEquiv (e : A ≃ᵐ B) (μ : Measure A) (f : A → ℝ)
    (hf : Measurable f) : (μ.tilted f).map e = (μ.map e).tilted (fun y => f (e.symm y)) := by
  have hZ : (∫ y, Real.exp (f (e.symm y)) ∂(μ.map e)) = ∫ x, Real.exp (f x) ∂μ := by
    simpa only [Function.comp_def, e.symm_apply_apply] using
      integral_map e.measurable.aemeasurable
        ((hf.comp e.symm.measurable).exp.aestronglyMeasurable)
  unfold Measure.tilted
  rw [Probability.map_withDensity_measurableEquiv e μ _ (hf.exp.div_const _).ennreal_ofReal, hZ]

/-- A positive scalar multiple of the base measure has the same normalized tilt. -/
theorem Probability.tilted_smul_pos {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ) {c : ℝ} (hc : 0 < c) :
    (ENNReal.ofReal c • μ).tilted f = μ.tilted f := by
  unfold Measure.tilted
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc.le, withDensity_smul_measure,
    ← withDensity_smul' (ENNReal.ofReal c) _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  change ENNReal.ofReal c * ENNReal.ofReal
    (Real.exp (f x) / (c * ∫ y, Real.exp (f y) ∂μ)) =
      ENNReal.ofReal (Real.exp (f x) / ∫ y, Real.exp (f y) ∂μ)
  rw [← ENNReal.ofReal_mul hc.le]
  congr 1
  by_cases hZ : (∫ y, Real.exp (f y) ∂μ) = 0
  · simp [hZ]
  · field_simp [hc.ne', hZ]


/-- A measurable pushforward commutes with a pulled-back density. -/
theorem Probability.map_withDensity_comp
    (μ : Measure A) (f : A → B) (hf : Measurable f) (g : B → ENNReal) (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    ← lintegral_indicator (hf hs), ← lintegral_indicator hs, lintegral_map (hg.indicator hs) hf]
  congr 1

/-- Pushforward of a tilt by a pulled-back exponent is the tilt of the pushforward. -/
theorem Probability.map_tilted_comp
    (μ : Measure A) (f : A → B) (hf : Measurable f) (φ : B → ℝ) (hφ : Measurable φ) :
    (μ.tilted (φ ∘ f)).map f = (μ.map f).tilted φ := by
  have hZ : (∫ y, Real.exp (φ y) ∂μ.map f) = ∫ x, Real.exp ((φ ∘ f) x) ∂μ := by
    simpa only [Function.comp_apply] using integral_map hf.aemeasurable hφ.exp.aestronglyMeasurable
  unfold Measure.tilted
  rw [hZ]
  simpa only [Function.comp_def] using Probability.map_withDensity_comp μ f hf
    (fun y => ENNReal.ofReal (Real.exp (φ y) / ∫ x, Real.exp ((φ ∘ f) x) ∂μ))
    (hφ.exp.div_const _).ennreal_ofReal

end MeasurableSpace

end TiltTransport

section TiltAbsoluteContinuity

variable {Ω : Type*} [MeasurableSpace Ω]

/--
A normalized exponential tilt has the same null sets as the base law (Mathlib absolute continuity in
both directions). -/
theorem Probability.tilted_null_iff (μ : Measure Ω) {φ : Ω → ℝ}
    (hi : Integrable (fun x => Real.exp (φ x)) μ) (s : Set Ω) : μ.tilted φ s = 0 ↔ μ s = 0 :=
  ⟨fun hs => absolutelyContinuous_tilted hi hs, fun hs => tilted_absolutelyContinuous μ φ hs⟩

/-- A normalized tilt has the same a.e. filter as the base law. -/
theorem Probability.ae_tilted_eq (μ : Measure Ω) {φ : Ω → ℝ}
    (hi : Integrable (fun x => Real.exp (φ x)) μ) : ae (μ.tilted φ) = ae μ :=
  le_antisymm (tilted_absolutelyContinuous μ φ).ae_le (absolutelyContinuous_tilted hi).ae_le

/-- A normalized tilt has the same topological support as the base law. -/
theorem Probability.support_tilted_eq [TopologicalSpace Ω] (μ : Measure Ω) {φ : Ω → ℝ}
    (hi : Integrable (fun x => Real.exp (φ x)) μ) : (μ.tilted φ).support = μ.support :=
  Set.Subset.antisymm (tilted_absolutelyContinuous μ φ).support_mono
    (absolutelyContinuous_tilted hi).support_mono

end TiltAbsoluteContinuity

section Translation

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  (ν : ProbabilityMeasure V) (c : V)

/-- The image of `ν` under the translation `x ↦ c + x`. -/
def Probability.translateLaw : ProbabilityMeasure V :=
  -- The measurability witness stays referenced so that the definition keeps the section instances
  -- it used before `ProbabilityMeasure.map` began taking the function itself (Mathlib v4.35).
  have _hmeas := measurable_const_add c
  ν.map (fun x ↦ c + x)

section TranslationLaws

omit [InnerProductSpace ℝ V]
theorem Probability.coe_translateLaw :
    (Probability.translateLaw ν c : Measure V) = (ν : Measure V).map (fun x ↦ c + x) := rfl

/-- The translation is measure preserving from `ν` to the translated law. -/
theorem Probability.measurePreserving_translate :
    MeasurePreserving (fun x ↦ c + x) (ν : Measure V) (Probability.translateLaw ν c : Measure V) :=
  ⟨measurable_const_add c, rfl⟩

/-- The inverse translation is measure preserving from the translated law back to `ν`. -/
theorem Probability.measurePreserving_translate_symm :
    MeasurePreserving (fun x ↦ -c + x) (Probability.translateLaw ν c : Measure V)
      (ν : Measure V) := by
  refine ⟨measurable_const_add _, ?_⟩
  rw [Probability.coe_translateLaw,
    Measure.map_map (measurable_const_add _) (measurable_const_add _)]
  have : ((fun x ↦ -c + x) ∘ fun x ↦ c + x) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

end TranslationLaws

section TranslationMoments

variable {V₁ : Type*} [NormedAddCommGroup V₁] [MeasurableSpace V₁] [BorelSpace V₁]

/-- Translation keeps a finite second moment. -/
theorem Probability.memLp_id_two_translateLaw
    (ν : ProbabilityMeasure V₁) (c : V₁) (h : MemLp id 2 (ν : Measure V₁)) :
    MemLp id 2 (translateLaw ν c : Measure V₁) := by
  rw [coe_translateLaw]
  exact (measurableEmbedding_addLeft c).memLp_map_measure_iff.mpr ((memLp_const c).add h)

end TranslationMoments

variable [CompleteSpace V]

/-- Translation does not change the covariance operator. -/
theorem Covariance.operator_translateLaw :
    Covariance.operator (Probability.translateLaw ν c : Measure V) =
      Covariance.operator (ν : Measure V) := by
  unfold Covariance.operator
  rw [Probability.coe_translateLaw, ProbabilityTheory.covarianceBilin_map_const_add]

end Translation

section LinearIsometry

variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
  {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
  (ν : ProbabilityMeasure V₁) (L : V₁ ≃ₗᵢ[ℝ] V₂)

/-- The image of `ν` under the linear isometric equivalence `L`. -/
def Probability.mapLinearIsometryEquiv : ProbabilityMeasure V₂ :=
  -- The measurability witness stays referenced so that the definition keeps the section instances
  -- it used before `ProbabilityMeasure.map` began taking the function itself (Mathlib v4.35).
  have _hmeas := L.continuous.measurable
  ν.map L

theorem Probability.coe_mapLinearIsometryEquiv :
    (Probability.mapLinearIsometryEquiv ν L : Measure V₂) = (ν : Measure V₁).map L :=
  rfl

/-- `L` is measure preserving from `ν` to its image law. -/
theorem Probability.measurePreserving_mapLinearIsometryEquiv :
    MeasurePreserving L (ν : Measure V₁) (Probability.mapLinearIsometryEquiv ν L : Measure V₂) :=
  ⟨L.continuous.measurable, rfl⟩

/-- `L⁻¹` is measure preserving from the image law back to `ν`. -/
theorem Probability.measurePreserving_mapLinearIsometryEquiv_symm :
    MeasurePreserving L.symm (Probability.mapLinearIsometryEquiv ν L : Measure V₂)
      (ν : Measure V₁) := by
  refine ⟨L.symm.continuous.measurable, ?_⟩
  rw [Probability.coe_mapLinearIsometryEquiv,
    Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
  have : (⇑L.symm ∘ ⇑L) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂]
  [SecondCountableTopology V₂]

/-- Without a finite second moment Mathlib's covariance operator is zero. -/
theorem Covariance.operator_of_not_memLp {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] (m : Measure W) (hm : ¬ MemLp id 2 m) : Covariance.operator m = 0 := by
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [Covariance.operator_inner, ProbabilityTheory.covarianceBilin_of_not_memLp hm]
  simp

section IsometricCovariance

omit [SecondCountableTopology V₁]
/--
Pushing a law forward along a linear isometric equivalence conjugates its covariance operator.
Without a second moment both operators are zero. -/
theorem Covariance.operator_map_linearIsometryEquiv (ν : Measure V₁) [IsFiniteMeasure ν]
    (L : V₁ ≃ₗᵢ[ℝ] V₂) :
    Covariance.operator (ν.map L) =
      ((L : V₁ →L[ℝ] V₂).comp (Covariance.operator ν)).comp (L.symm : V₂ →L[ℝ] V₁) := by
  have hcoe : ⇑(L : V₁ →L[ℝ] V₂) = ⇑L := rfl
  by_cases h : MemLp id 2 ν
  · ext u
    apply ext_inner_right ℝ
    intro v
    rw [Covariance.operator_inner, ← hcoe,
      ProbabilityTheory.covarianceBilin_map h (L : V₁ →L[ℝ] V₂),
      LinearIsometryEquiv.adjoint_eq_symm, ← Covariance.operator_inner]
    simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'']
    rw [← L.inner_map_map (Covariance.operator ν (L.symm u)) (L.symm v), L.apply_symm_apply]
  · have h' : ¬MemLp id 2 (ν.map L) := by
      intro h'
      apply h
      have h1 : MemLp (fun x ↦ L x) 2 ν :=
        (memLp_map_measure_iff aestronglyMeasurable_id L.continuous.measurable.aemeasurable).mp
          h'
      have h2 := (L.symm : V₂ →L[ℝ] V₁).comp_memLp' h1
      have h3 : (⇑(L.symm : V₂ →L[ℝ] V₁) ∘ fun x ↦ L x) = id := by
        funext x
        simp
      rwa [h3] at h2
    rw [Covariance.operator_of_not_memLp ν h, Covariance.operator_of_not_memLp (ν.map L) h']
    simp

/-- The covariance operator of the image law is the conjugate of the covariance operator of `ν`. -/
theorem Covariance.operator_mapLinearIsometryEquiv :
    Covariance.operator (Probability.mapLinearIsometryEquiv ν L : Measure V₂) =
      ((L : V₁ →L[ℝ] V₂).comp (Covariance.operator (ν : Measure V₁))).comp (L.symm : V₂ →L[ℝ] V₁) :=
  Covariance.operator_map_linearIsometryEquiv (ν : Measure V₁) L

/-- The covariance quadratic form of the image law, read through `L⁻¹`. -/
theorem Covariance.inner_operator_mapLinearIsometryEquiv (w : V₂) :
    inner ℝ (Covariance.operator (Probability.mapLinearIsometryEquiv ν L : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν : Measure V₁) (L.symm w)) (L.symm w) := by
  rw [Covariance.operator_mapLinearIsometryEquiv]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'']
  rw [← L.inner_map_map (Covariance.operator (ν : Measure V₁) (L.symm w)) (L.symm w),
    L.apply_symm_apply]

/-- The covariance quadratic form of `ν`, read through `L`. -/
theorem Covariance.inner_operator_mapLinearIsometryEquiv_apply (w : V₁) :
    inner ℝ (Covariance.operator (ν : Measure V₁) w) w =
      inner ℝ (Covariance.operator (Probability.mapLinearIsometryEquiv ν L : Measure V₂) (L w))
        (L w) := by
  rw [Covariance.inner_operator_mapLinearIsometryEquiv, L.symm_apply_apply]

end IsometricCovariance

end LinearIsometry

section ContinuousLinearEquiv

variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
  {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
  (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)

/-- The image of `ν` under the continuous linear equivalence `T`. -/
def Probability.mapContinuousLinearEquiv : ProbabilityMeasure V₂ :=
  -- The measurability witness stays referenced so that the definition keeps the section instances
  -- it used before `ProbabilityMeasure.map` began taking the function itself (Mathlib v4.35).
  have _hmeas := T.continuous.measurable
  ν.map T

theorem Probability.coe_mapContinuousLinearEquiv :
    (Probability.mapContinuousLinearEquiv ν T : Measure V₂) = (ν : Measure V₁).map T :=
  rfl

/-- `T` is measure preserving from `ν` to its image law. -/
theorem Probability.measurePreserving_mapContinuousLinearEquiv :
    MeasurePreserving T (ν : Measure V₁) (Probability.mapContinuousLinearEquiv ν T : Measure V₂) :=
  ⟨T.continuous.measurable, rfl⟩

/-- `T⁻¹` is measure preserving from the image law back to `ν`. -/
theorem Probability.measurePreserving_mapContinuousLinearEquiv_symm :
    MeasurePreserving T.symm (Probability.mapContinuousLinearEquiv ν T : Measure V₂)
      (ν : Measure V₁) := by
  refine ⟨T.symm.continuous.measurable, ?_⟩
  rw [Probability.coe_mapContinuousLinearEquiv,
    Measure.map_map T.symm.continuous.measurable T.continuous.measurable]
  have : (⇑T.symm ∘ ⇑T) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂]
  [SecondCountableTopology V₂]

section EquivalentCovariance

omit [SecondCountableTopology V₁]
/--
Pushing a law forward along a continuous linear equivalence conjugates its covariance operator
by the map and its adjoint. Without a second moment both operators are zero. -/
theorem Covariance.operator_map_continuousLinearEquiv (ν : Measure V₁) [IsFiniteMeasure ν]
    (T : V₁ ≃L[ℝ] V₂) :
    Covariance.operator (ν.map T) =
      ((T : V₁ →L[ℝ] V₂).comp (Covariance.operator ν)).comp (T : V₁ →L[ℝ] V₂).adjoint := by
  have hcoe : ⇑(T : V₁ →L[ℝ] V₂) = ⇑T := rfl
  by_cases h : MemLp id 2 ν
  · ext u
    apply ext_inner_right ℝ
    intro v
    rw [Covariance.operator_inner, ← hcoe,
      ProbabilityTheory.covarianceBilin_map h (T : V₁ →L[ℝ] V₂), ← Covariance.operator_inner]
    simp only [ContinuousLinearMap.comp_apply]
    exact
      ContinuousLinearMap.adjoint_inner_right (T : V₁ →L[ℝ] V₂)
        (Covariance.operator ν ((T : V₁ →L[ℝ] V₂).adjoint u)) v
  · have h' : ¬MemLp id 2 (ν.map T) := by
      intro h'
      apply h
      have h1 : MemLp (fun x ↦ T x) 2 ν :=
        (memLp_map_measure_iff aestronglyMeasurable_id T.continuous.measurable.aemeasurable).mp
          h'
      have h2 := (T.symm : V₂ →L[ℝ] V₁).comp_memLp' h1
      have h3 : (⇑(T.symm : V₂ →L[ℝ] V₁) ∘ fun x ↦ T x) = id := by
        funext x
        simp
      rwa [h3] at h2
    rw [Covariance.operator_of_not_memLp ν h, Covariance.operator_of_not_memLp (ν.map T) h']
    simp

/-- The covariance operator of the image law. -/
theorem Covariance.operator_mapContinuousLinearEquiv :
    Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂) =
      ((T : V₁ →L[ℝ] V₂).comp (Covariance.operator (ν : Measure V₁))).comp
        (T : V₁ →L[ℝ] V₂).adjoint :=
  Covariance.operator_map_continuousLinearEquiv (ν : Measure V₁) T

/-- The covariance quadratic form of the image law, read through the adjoint. -/
theorem Covariance.inner_operator_mapContinuousLinearEquiv (w : V₂) :
    inner ℝ (Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂) w) w =
      inner ℝ (Covariance.operator (ν : Measure V₁) ((T : V₁ →L[ℝ] V₂).adjoint w))
        ((T : V₁ →L[ℝ] V₂).adjoint w) := by
  rw [Covariance.operator_mapContinuousLinearEquiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.adjoint_inner_right (T : V₁ →L[ℝ] V₂) _ w).symm

/-- The covariance quadratic form of `ν`, read through the adjoint of the inverse. -/
theorem Covariance.inner_operator_mapContinuousLinearEquiv_symm (w : V₁) :
    inner ℝ (Covariance.operator (ν : Measure V₁) w) w =
      inner ℝ (Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂)
        ((T.symm : V₂ →L[ℝ] V₁).adjoint w)) ((T.symm : V₂ →L[ℝ] V₁).adjoint w) := by
  rw [Covariance.inner_operator_mapContinuousLinearEquiv]
  have hT : (T : V₁ →L[ℝ] V₂).adjoint ((T.symm : V₂ →L[ℝ] V₁).adjoint w) = w := by
    have hcomp : (T.symm : V₂ →L[ℝ] V₁).comp (T : V₁ →L[ℝ] V₂) = ContinuousLinearMap.id ℝ V₁ := by
      ext x
      simp
    have := congrArg (fun A : V₁ →L[ℝ] V₁ ↦ A.adjoint w) hcomp
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] using this
  rw [hT]

/-- The barycenter of the image law is the image of the barycenter. -/
theorem Probability.integral_id_mapContinuousLinearEquiv
    (hint : Integrable id (ν : Measure V₁)) :
    ∫ y, y ∂(Probability.mapContinuousLinearEquiv ν T : Measure V₂) =
      T (∫ x, x ∂(ν : Measure V₁)) := by
  rw [Probability.coe_mapContinuousLinearEquiv,
    integral_map T.continuous.measurable.aemeasurable continuous_id'.aestronglyMeasurable]
  have hint' : Integrable (fun x : V₁ ↦ x) (ν : Measure V₁) := hint
  exact (T : V₁ →L[ℝ] V₂).integral_comp_comm hint'

end EquivalentCovariance

omit [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] in
/-- The image law keeps a finite second moment. -/
theorem Probability.memLp_id_two_mapContinuousLinearEquiv (h : MemLp id 2 (ν : Measure V₁)) :
    MemLp id 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂) := by
  rw [Probability.coe_mapContinuousLinearEquiv, memLp_map_measure_iff aestronglyMeasurable_id
    T.continuous.measurable.aemeasurable]
  exact (T : V₁ →L[ℝ] V₂).comp_memLp' h

variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]

section AffineSupports

omit [CompleteSpace V₁] [CompleteSpace V₂] [FiniteDimensional ℝ V₁]
/-- The affine support of the image law is the image of the affine support. -/
theorem Probability.affineSupport_mapContinuousLinearEquiv :
    affineSupport (mapContinuousLinearEquiv ν T) =
      (affineSupport ν).map (T : V₁ →ₗ[ℝ] V₂).toAffineMap := by
  apply le_antisymm
  · apply affineSupport_le_of_ae_mem
    · exact ((affineSupport ν).map (T : V₁ →ₗ[ℝ] V₂).toAffineMap).isClosed_of_finiteDimensional
    · rw [coe_mapContinuousLinearEquiv]
      refine
        (ae_map_iff T.continuous.measurable.aemeasurable
              ((affineSupport ν).map
                  (T : V₁ →ₗ[ℝ] V₂).toAffineMap).isClosed_of_finiteDimensional.measurableSet).2
          ?_
      filter_upwards [ae_mem_affineSupport ν] with x hx
      exact ⟨x, hx, rfl⟩
  · rw [AffineSubspace.map_le_iff_le_comap]
    apply affineSupport_le_of_ae_mem
    · change
        IsClosed
          ((fun x : V₁ ↦ T x) ⁻¹' (affineSupport (mapContinuousLinearEquiv ν T) : Set V₂))
      exact (isClosed_affineSupport _).preimage T.continuous
    · have h := ae_mem_affineSupport (mapContinuousLinearEquiv ν T)
      rw [coe_mapContinuousLinearEquiv] at h
      filter_upwards [ae_of_ae_map T.continuous.measurable.aemeasurable h] with x hx
      exact hx

/-- A full affine support stays full under a continuous linear equivalence. -/
theorem Probability.affineSupport_mapContinuousLinearEquiv_eq_top (h : affineSupport ν = ⊤) :
    affineSupport (mapContinuousLinearEquiv ν T) = ⊤ := by
  rw [affineSupport_mapContinuousLinearEquiv, h]
  exact AffineMap.map_top_of_surjective _ T.surjective

end AffineSupports

end ContinuousLinearEquiv

end FunctionalInequalities
