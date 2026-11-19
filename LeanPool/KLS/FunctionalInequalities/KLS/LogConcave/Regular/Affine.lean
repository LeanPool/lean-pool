/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Regular.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Regular potentials under affine changes of variables

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): the regular class (12) is stable under
affine changes of variables, which is what centering and whitening a regular law use. For a regular
potential `V` and an invertible affine map `x ↦ L x + c`, the potential `V ∘ (L · + c)` is regular
(`Regular`), its normalizing constant is `|det L|⁻¹` times that of `V`, and its law is exactly the
image of the law of `V` under `y ↦ L⁻¹(y − c)`, i.e. a translation followed by the continuous linear
equivalence `L⁻¹`. No whitening operator is chosen here.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace ContDiff

noncomputable section

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The affine homeomorphism `x ↦ L x + c`. -/
def affineHomeomorph (L : E ≃L[ℝ] E) (c : E) : E ≃ₜ E :=
  L.toHomeomorph.trans (Homeomorph.addRight c)

/-- The inverse affine map `y ↦ L⁻¹(y − c)` as a measurable equivalence. -/
def inverseAffineEquiv (L : E ≃L[ℝ] E) (c : E) : E ≃ᵐ E :=
  (affineHomeomorph L c).symm.toMeasurableEquiv

section InverseAffineEvaluation

omit [CompleteSpace E] [FiniteDimensional ℝ E]

theorem inverseAffineEquiv_apply (L : E ≃L[ℝ] E) (c y : E) :
    inverseAffineEquiv L c y = L.symm (y - c) := by
  change L.symm (y + -c) = L.symm (y - c)
  rw [sub_eq_add_neg]

theorem inverseAffineEquiv_symm_apply (L : E ≃L[ℝ] E) (c x : E) :
    (inverseAffineEquiv L c).symm x = L x + c := rfl

end InverseAffineEvaluation

omit [CompleteSpace E] in
/-- Lebesgue measure under the inverse affine map scales by `|det L⁻¹|⁻¹`. -/
theorem inverseAffine_map_volume (L : E ≃L[ℝ] E) (c : E) :
    (volume : Measure E).map (inverseAffineEquiv L c) =
      ENNReal.ofReal |(LinearMap.det (L.symm : E →ₗ[ℝ] E))⁻¹| • volume := by
  have hdet : LinearMap.det (L.symm : E →ₗ[ℝ] E) ≠ 0 := L.symm.toLinearEquiv.isUnit_det'.ne_zero
  have ht : (volume : Measure E).map (fun y => y - c) = volume := by
    simp_rw [sub_eq_add_neg]
    exact Measure.IsAddRightInvariant.map_add_right_eq_self (-c)
  have heq : (inverseAffineEquiv L c : E → E) =
      (fun y => L.symm y) ∘ (fun y => y - c) := by
    funext y
    exact inverseAffineEquiv_apply L c y
  rw [heq, ← Measure.map_map L.symm.continuous.measurable (by fun_prop), ht]
  exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet

section RegularAffineLaws

variable {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)

include hV in
/--
**The law of `V ∘ (L · + c)` is the image of the law of `V` under `y ↦ L⁻¹(y − c)`** (the Jacobian
constant cancels in the normalization). -/
theorem RegularPotential.law_comp_affine (L : E ≃L[ℝ] E) (c : E) :
    ((RegularPotential.comp_affine hV L c).law : Measure E) =
      (hV.law : Measure E).map (fun y => L.symm (y - c)) := by
  let e := inverseAffineEquiv L c
  have ht :=
    Probability.map_tilted_measurableEquiv e (volume : Measure E) (-V)
      hV.temperate.1.continuous.neg.measurable
  have hmap := inverseAffine_map_volume L c
  have hdet : LinearMap.det (L.symm : E →ₗ[ℝ] E) ≠ 0 := L.symm.toLinearEquiv.isUnit_det'.ne_zero
  have hJ : 0 < |(LinearMap.det (L.symm : E →ₗ[ℝ] E))⁻¹| := abs_pos.2 (inv_ne_zero hdet)
  rw [hmap, Probability.tilted_smul_pos _ _ hJ] at ht
  have hf : (fun y => (-V) (e.symm y)) = -fun x => V (L x + c) := by
    funext y
    rw [show e.symm y = L y + c from inverseAffineEquiv_symm_apply L c y]
    rfl
  rw [hf] at ht
  have heq : (e : E → E) = fun y => L.symm (y - c) := funext (inverseAffineEquiv_apply L c)
  rw [heq] at ht
  exact ht.symm

omit [CompleteSpace E] in
include hV in
/-- The normalizing constant of `V ∘ (L · + c)` is `|det L|⁻¹` times that of `V`. -/
theorem RegularPotential.integral_exp_neg_comp_affine (L : E ≃L[ℝ] E) (c : E) :
    (∫ x, Real.exp (-V (L x + c)) ∂(volume : Measure E)) =
      |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹| * ∫ y, Real.exp (-V y) ∂(volume : Measure E) := by
  let e := inverseAffineEquiv L c
  have hmap := inverseAffine_map_volume L c
  have hdet : LinearMap.det (L : E →ₗ[ℝ] E) ≠ 0 := L.toLinearEquiv.isUnit_det'.ne_zero
  have hj : |(LinearMap.det (L.symm : E →ₗ[ℝ] E))⁻¹| = |LinearMap.det (L : E →ₗ[ℝ] E)| := by
    change
      |(LinearMap.det (L.toLinearEquiv.symm : E →ₗ[ℝ] E))⁻¹| =
        |LinearMap.det (L.toLinearEquiv : E →ₗ[ℝ] E)|
    rw [LinearEquiv.det_coe_symm L.toLinearEquiv, inv_inv]
  rw [hj] at hmap
  have hcont : Continuous (fun y : E => Real.exp (-V (L y + c))) :=
    Real.continuous_exp.comp
      ((hV.temperate.1.continuous.comp (L.continuous.add continuous_const)).neg)
  have hInt :=
    integral_map (μ := (volume : Measure E)) e.measurable.aemeasurable
      hcont.aestronglyMeasurable
  have hcanc : (fun y => Real.exp (-V (L (e y) + c))) = fun y => Real.exp (-V y) := by
    funext y
    rw [inverseAffineEquiv_apply, L.apply_symm_apply, sub_add_cancel]
  change
    (∫ y, Real.exp (-V (L y + c)) ∂(volume : Measure E).map e) =
      ∫ y, Real.exp (-V (L (e y) + c)) ∂volume at hInt
  rw [hcanc, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at hInt
  have hJ : |LinearMap.det (L : E →ₗ[ℝ] E)| ≠ 0 := abs_ne_zero.2 hdet
  have heq :
    (∫ x, Real.exp (-V (L x + c)) ∂(volume : Measure E)) =
      (∫ y, Real.exp (-V y) ∂(volume : Measure E)) / |LinearMap.det (L : E →ₗ[ℝ] E)| := by
    apply (eq_div_iff hJ).2
    simpa only [smul_eq_mul, mul_comm] using hInt
  rw [heq, abs_inv]
  ring

include hV in
/--
The law of `V ∘ (L · + c)` as a translation followed by the continuous linear equivalence `L⁻¹`. -/
theorem RegularPotential.law_comp_affine_eq_map (L : E ≃L[ℝ] E) (c : E) :
    (RegularPotential.comp_affine hV L c).law =
      Probability.mapContinuousLinearEquiv (Probability.translateLaw hV.law (-c)) L.symm := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [RegularPotential.law_comp_affine hV L c, Probability.coe_mapContinuousLinearEquiv,
    Probability.coe_translateLaw, Measure.map_map L.symm.continuous.measurable (by fun_prop)]
  congr 1
  funext y
  change L.symm (y - c) = L.symm (-c + y)
  congr 1
  abel

end RegularAffineLaws

end FunctionalInequalities.KLS

end
