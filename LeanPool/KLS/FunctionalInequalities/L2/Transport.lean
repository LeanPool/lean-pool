/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Transport
public import LeanPool.KLS.FunctionalInequalities.L2.MeanVariance

/-! # Pullback of real L² classes

Each `pullback` composes with the displayed map, from the L² space of the image law back
to the L² space of the source law. `pullbackInv` composes with the inverse map.
The construction uses Mathlib `Lp.compMeasurePreservingₗᵢ`; `pullbackEquiv` packages its inverse.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace

namespace FunctionalInequalities.L2

universe u v

namespace Translation

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  (ν : ProbabilityMeasure V) (c : V)

/-- Pullback of `L²` classes along the translation. -/
def pullback : Lp ℝ 2 (Probability.translateLaw ν c : Measure V) →ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x ↦ c + x) (Probability.measurePreserving_translate ν c)

/-- Pullback of `L²` classes along the inverse translation. -/
def pullbackInv : Lp ℝ 2 (ν : Measure V) →ₗᵢ[ℝ] Lp ℝ 2 (Probability.translateLaw ν c : Measure V) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x ↦ -c + x) (Probability.measurePreserving_translate_symm ν c)

section TranslationPullbacks

omit [InnerProductSpace ℝ V]
theorem pullback_coeFn (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    pullback ν c f =ᵐ[(ν : Measure V)] fun x ↦ f (c + x) :=
  Lp.coeFn_compMeasurePreserving f (Probability.measurePreserving_translate ν c)

theorem pullbackInv_pullback (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    pullbackInv ν c (pullback ν c f) = f := by
  change
    Lp.compMeasurePreserving (fun x ↦ -c + x) (Probability.measurePreserving_translate_symm ν c)
        (Lp.compMeasurePreserving (fun x ↦ c + x) (Probability.measurePreserving_translate ν c)
          f) =
      f
  rw [←
    Lp.compMeasurePreserving_comp_apply f (Probability.measurePreserving_translate ν c)
      (Probability.measurePreserving_translate_symm ν c)]
  apply Subtype.ext
  change
    f.1.compMeasurePreserving ((fun x ↦ c + x) ∘ fun x ↦ -c + x)
        ((Probability.measurePreserving_translate ν c).comp
          (Probability.measurePreserving_translate_symm ν c)) =
      f.1
  have hae :
    ((fun x ↦ c + x) ∘ fun x ↦ -c + x) =ᵐ[(Probability.translateLaw ν c : Measure V)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

theorem pullback_pullbackInv (f : Lp ℝ 2 (ν : Measure V)) :
    pullback ν c (pullbackInv ν c f) = f := by
  change
    Lp.compMeasurePreserving (fun x ↦ c + x) (Probability.measurePreserving_translate ν c)
        (Lp.compMeasurePreserving (fun x ↦ -c + x)
          (Probability.measurePreserving_translate_symm ν c) f) =
      f
  rw [←
    Lp.compMeasurePreserving_comp_apply f (Probability.measurePreserving_translate_symm ν c)
      (Probability.measurePreserving_translate ν c)]
  apply Subtype.ext
  change
    f.1.compMeasurePreserving ((fun x ↦ -c + x) ∘ fun x ↦ c + x)
        ((Probability.measurePreserving_translate_symm ν c).comp
          (Probability.measurePreserving_translate ν c)) =
      f.1
  have hae : ((fun x ↦ -c + x) ∘ fun x ↦ c + x) =ᵐ[(ν : Measure V)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

end TranslationPullbacks

/-- Pullback along the translation as a linear isometric equivalence of real `L²` spaces. -/
def pullbackEquiv :
    Lp ℝ 2 (Probability.translateLaw ν c : Measure V) ≃ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V)
    where
  toFun := pullback ν c
  invFun := pullbackInv ν c
  left_inv := pullbackInv_pullback ν c
  right_inv := pullback_pullbackInv ν c
  map_add' := map_add (pullback ν c)
  map_smul' := map_smul (pullback ν c)
  norm_map' := norm_map (pullback ν c)

omit [InnerProductSpace ℝ V] in
@[simp]
theorem pullbackEquiv_apply (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    pullbackEquiv ν c f = pullback ν c f := rfl

omit [InnerProductSpace ℝ V] in
@[simp]
theorem pullbackEquiv_symm_apply (f : Lp ℝ 2 (ν : Measure V)) :
    (pullbackEquiv ν c).symm f = pullbackInv ν c f := rfl

omit [InnerProductSpace ℝ V] in
/-- Pullback along the translation preserves the intrinsic `L²` variance. -/
theorem variance_pullbackEquiv
    (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    L2.variance ν (pullbackEquiv ν c f) = L2.variance (Probability.translateLaw ν c) f := by
  apply NNReal.eq
  rw [L2.coe_variance_eq_pointwise, L2.coe_variance_eq_pointwise, pullbackEquiv_apply,
    ProbabilityTheory.variance_congr (pullback_coeFn ν c f)]
  exact (Probability.measurePreserving_translate ν c).variance_fun_comp
    (Lp.aestronglyMeasurable f).aemeasurable

end Translation

namespace LinearIsometry

variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
  {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
  (ν : ProbabilityMeasure V₁) (L : V₁ ≃ₗᵢ[ℝ] V₂)

/-- Pullback of `L²` classes along `L`. -/
def pullback :
    Lp ℝ 2 (Probability.mapLinearIsometryEquiv ν L : Measure V₂) →ₗᵢ[ℝ]
      Lp ℝ 2 (ν : Measure V₁) :=
  Lp.compMeasurePreservingₗᵢ ℝ L (Probability.measurePreserving_mapLinearIsometryEquiv ν L)

/-- Pullback of `L²` classes along `L⁻¹`. -/
def pullbackInv :
    Lp ℝ 2 (ν : Measure V₁) →ₗᵢ[ℝ]
      Lp ℝ 2 (Probability.mapLinearIsometryEquiv ν L : Measure V₂) :=
  Lp.compMeasurePreservingₗᵢ ℝ L.symm
    (Probability.measurePreserving_mapLinearIsometryEquiv_symm ν L)

theorem pullback_coeFn (f : Lp ℝ 2 (Probability.mapLinearIsometryEquiv ν L : Measure V₂)) :
    pullback ν L f =ᵐ[(ν : Measure V₁)] fun x ↦ f (L x) :=
  Lp.coeFn_compMeasurePreserving f (Probability.measurePreserving_mapLinearIsometryEquiv ν L)

theorem pullbackInv_pullback
    (f : Lp ℝ 2 (Probability.mapLinearIsometryEquiv ν L : Measure V₂)) :
    pullbackInv ν L (pullback ν L f) = f := by
  change
    Lp.compMeasurePreserving L.symm
        (Probability.measurePreserving_mapLinearIsometryEquiv_symm ν L)
        (Lp.compMeasurePreserving L (Probability.measurePreserving_mapLinearIsometryEquiv ν L)
          f) =
      f
  rw [←
    Lp.compMeasurePreserving_comp_apply f
      (Probability.measurePreserving_mapLinearIsometryEquiv ν L)
      (Probability.measurePreserving_mapLinearIsometryEquiv_symm ν L)]
  apply Subtype.ext
  change
    f.1.compMeasurePreserving (⇑L ∘ ⇑L.symm)
        ((Probability.measurePreserving_mapLinearIsometryEquiv ν L).comp
          (Probability.measurePreserving_mapLinearIsometryEquiv_symm ν L)) =
      f.1
  have hae : (⇑L ∘ ⇑L.symm) =ᵐ[(Probability.mapLinearIsometryEquiv ν L : Measure V₂)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

theorem pullback_pullbackInv (f : Lp ℝ 2 (ν : Measure V₁)) :
    pullback ν L (pullbackInv ν L f) = f := by
  change
    Lp.compMeasurePreserving L (Probability.measurePreserving_mapLinearIsometryEquiv ν L)
        (Lp.compMeasurePreserving L.symm
          (Probability.measurePreserving_mapLinearIsometryEquiv_symm ν L) f) =
      f
  rw [←
    Lp.compMeasurePreserving_comp_apply f
      (Probability.measurePreserving_mapLinearIsometryEquiv_symm ν L)
      (Probability.measurePreserving_mapLinearIsometryEquiv ν L)]
  apply Subtype.ext
  change
    f.1.compMeasurePreserving (⇑L.symm ∘ ⇑L)
        ((Probability.measurePreserving_mapLinearIsometryEquiv_symm ν L).comp
          (Probability.measurePreserving_mapLinearIsometryEquiv ν L)) =
      f.1
  have hae : (⇑L.symm ∘ ⇑L) =ᵐ[(ν : Measure V₁)] id := Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

/-- Pullback along `L` as a linear isometric equivalence of real `L²` spaces. -/
def pullbackEquiv :
    Lp ℝ 2 (Probability.mapLinearIsometryEquiv ν L : Measure V₂) ≃ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V₁)
    where
  toFun := pullback ν L
  invFun := pullbackInv ν L
  left_inv := pullbackInv_pullback ν L
  right_inv := pullback_pullbackInv ν L
  map_add' := map_add (pullback ν L)
  map_smul' := map_smul (pullback ν L)
  norm_map' := norm_map (pullback ν L)

@[simp]
theorem pullbackEquiv_apply (f : Lp ℝ 2 (Probability.mapLinearIsometryEquiv ν L : Measure V₂)) :
    pullbackEquiv ν L f = pullback ν L f := rfl

@[simp]
theorem pullbackEquiv_symm_apply (f : Lp ℝ 2 (ν : Measure V₁)) :
    (pullbackEquiv ν L).symm f = pullbackInv ν L f := rfl

/-- Pullback along `L` preserves the intrinsic `L²` variance. -/
theorem variance_pullbackEquiv
    (f : Lp ℝ 2 (Probability.mapLinearIsometryEquiv ν L : Measure V₂)) :
    L2.variance ν (pullbackEquiv ν L f) =
      L2.variance (Probability.mapLinearIsometryEquiv ν L) f := by
  apply NNReal.eq
  rw [L2.coe_variance_eq_pointwise, L2.coe_variance_eq_pointwise, pullbackEquiv_apply,
    ProbabilityTheory.variance_congr (pullback_coeFn ν L f)]
  exact
    (Probability.measurePreserving_mapLinearIsometryEquiv ν L).variance_fun_comp
      (Lp.aestronglyMeasurable f).aemeasurable

end LinearIsometry

namespace ContinuousLinearEquiv

variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
  {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
  (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)

/-- Pullback of `L²` classes along `T`. -/
def pullback :
    Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂) →ₗᵢ[ℝ]
      Lp ℝ 2 (ν : Measure V₁) :=
  Lp.compMeasurePreservingₗᵢ ℝ T (Probability.measurePreserving_mapContinuousLinearEquiv ν T)

/-- Pullback of `L²` classes along `T⁻¹`. -/
def pullbackInv :
    Lp ℝ 2 (ν : Measure V₁) →ₗᵢ[ℝ]
      Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂) :=
  Lp.compMeasurePreservingₗᵢ ℝ T.symm
    (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T)

theorem pullback_coeFn (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    pullback ν T f =ᵐ[(ν : Measure V₁)] fun x ↦ f (T x) :=
  Lp.coeFn_compMeasurePreserving f (Probability.measurePreserving_mapContinuousLinearEquiv ν T)

theorem pullbackInv_pullback
    (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    pullbackInv ν T (pullback ν T f) = f := by
  change
    Lp.compMeasurePreserving T.symm
        (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T)
        (Lp.compMeasurePreserving T (Probability.measurePreserving_mapContinuousLinearEquiv ν T)
          f) =
      f
  rw [←
    Lp.compMeasurePreserving_comp_apply f
      (Probability.measurePreserving_mapContinuousLinearEquiv ν T)
      (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T)]
  apply Subtype.ext
  change
    f.1.compMeasurePreserving (⇑T ∘ ⇑T.symm)
        ((Probability.measurePreserving_mapContinuousLinearEquiv ν T).comp
          (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T)) =
      f.1
  have hae : (⇑T ∘ ⇑T.symm) =ᵐ[(Probability.mapContinuousLinearEquiv ν T : Measure V₂)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

theorem pullback_pullbackInv (f : Lp ℝ 2 (ν : Measure V₁)) :
    pullback ν T (pullbackInv ν T f) = f := by
  change
    Lp.compMeasurePreserving T (Probability.measurePreserving_mapContinuousLinearEquiv ν T)
        (Lp.compMeasurePreserving T.symm
          (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T) f) =
      f
  rw [←
    Lp.compMeasurePreserving_comp_apply f
      (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T)
      (Probability.measurePreserving_mapContinuousLinearEquiv ν T)]
  apply Subtype.ext
  change
    f.1.compMeasurePreserving (⇑T.symm ∘ ⇑T)
        ((Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T).comp
          (Probability.measurePreserving_mapContinuousLinearEquiv ν T)) =
      f.1
  have hae : (⇑T.symm ∘ ⇑T) =ᵐ[(ν : Measure V₁)] id := Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

/-- Pullback along `T` as a linear isometric equivalence of real `L²` spaces. -/
def pullbackEquiv :
    Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (ν : Measure V₁)
    where
  toFun := pullback ν T
  invFun := pullbackInv ν T
  left_inv := pullbackInv_pullback ν T
  right_inv := pullback_pullbackInv ν T
  map_add' := map_add (pullback ν T)
  map_smul' := map_smul (pullback ν T)
  norm_map' := norm_map (pullback ν T)

@[simp]
theorem pullbackEquiv_apply (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    pullbackEquiv ν T f = pullback ν T f := rfl

@[simp]
theorem pullbackEquiv_symm_apply (f : Lp ℝ 2 (ν : Measure V₁)) :
    (pullbackEquiv ν T).symm f = pullbackInv ν T f := rfl

/-- Pullback along `T` preserves the intrinsic `L²` variance. -/
theorem variance_pullbackEquiv
    (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    L2.variance ν (pullbackEquiv ν T f) =
      L2.variance (Probability.mapContinuousLinearEquiv ν T) f := by
  apply NNReal.eq
  rw [L2.coe_variance_eq_pointwise, L2.coe_variance_eq_pointwise, pullbackEquiv_apply,
    ProbabilityTheory.variance_congr (pullback_coeFn ν T f)]
  exact
    (Probability.measurePreserving_mapContinuousLinearEquiv ν T).variance_fun_comp
      (Lp.aestronglyMeasurable f).aemeasurable

end ContinuousLinearEquiv

end FunctionalInequalities.L2
