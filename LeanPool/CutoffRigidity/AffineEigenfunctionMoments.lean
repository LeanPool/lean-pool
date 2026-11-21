/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.AffineEigenfunctionSplitting
public import LeanPool.CutoffRigidity.AffineGradient
public import LeanPool.CutoffRigidity.Gibbs
public import LeanPool.CutoffRigidity.GaussianMoments
public import Mathlib.Probability.HasLaw
public import LeanPool.CutoffRigidity.TransportMoments

/-!
# The Gaussian law and moments of an affine eigenfunction

The actual pointwise eigenfunction equation is used to derive a Gaussian
factor of the Gibbs measure. Projection of that factor then supplies the
Gaussian law, L² membership, and gradient normalization of the affine
function, without assuming its law or spectral-domain membership.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A nonconstant affine pointwise eigenfunction under the actual normalized
Gibbs law has the centered Gaussian law forced by its gradient direction. -/
theorem affine_eigenfunction_hasLaw_gaussian
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (ha : a ≠ 0) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
        -ρ * (inner ℝ a x + b))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    HasLaw (fun x : E => inner ℝ a x + b)
      (gaussianReal 0 (‖a‖ ^ 2 / ρ).toNNReal) (gibbsMeasure volume V) := by
  obtain ⟨A, hA, ν, hν, hfactor⟩ :=
    affine_eigenfunction_gibbs_factor V hV a ha b ρ hρ heigen hprob
  let := hν
  change (gibbsMeasure volume V).map
    (fun x => (A (x + (b / ‖a‖) • (‖a‖⁻¹ • a))).ofLp) = _ at hfactor
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hv : ‖‖a‖⁻¹ • a‖ = 1 := by simp [norm_smul, hna]
  have hfst (y : E) : (A y).ofLp.1 = inner ℝ (‖a‖⁻¹ • a) y := by
    have h := A.inner_map_eq_flip y
      (WithLp.toLp 2 (1, (0 : (Submodule.span ℝ {‖a‖⁻¹ • a})ᗮ)))
    rw [hA] at h
    simpa [WithLp.prod_inner_apply, real_inner_comm] using h
  have hid (x : E) :
      ‖a‖ * (A (x + (b / ‖a‖) • (‖a‖⁻¹ • a))).ofLp.1 = inner ℝ a x + b := by
    rw [hfst, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hv,
      real_inner_smul_left]
    field_simp
  refine { aemeasurable := ?_, map_eq := ?_ }
  · exact (by fun_prop : Measurable (fun x : E => inner ℝ a x + b)).aemeasurable
  · calc
      _ = (((gibbsMeasure volume V).map
          (fun x => (A (x + (b / ‖a‖) • (‖a‖⁻¹ • a))).ofLp))).map
            (fun z => ‖a‖ * z.1) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          congr 1
          funext x
          exact (hid x).symm
      _ = ((gaussianReal 0 (ρ⁻¹).toNNReal).prod ν).map (fun z => ‖a‖ * z.1) := by
          rw [hfactor]
      _ = (gaussianReal 0 (ρ⁻¹).toNNReal).map (fun z => ‖a‖ * z) := by
          change ((gaussianReal 0 (ρ⁻¹).toNNReal).prod ν).map
            ((fun z : ℝ => ‖a‖ * z) ∘ Prod.fst) = _
          rw [← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod]
          simp
      _ = gaussianReal 0 (‖a‖ ^ 2 / ρ).toNNReal := by
          rw [gaussianReal_map_const_mul]
          simp only [mul_zero]
          congr 1
          apply NNReal.eq
          simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal',
            max_eq_left (inv_nonneg.mpr hρ.le), div_eq_mul_inv,
            max_eq_left (mul_nonneg (sq_nonneg ‖a‖) (inv_nonneg.mpr hρ.le))]

/-- L² integrability is derived from the Gaussian factor, rather than added
as a premise to the pointwise eigenfunction equation. -/
theorem affine_eigenfunction_memLp
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (ha : a ≠ 0) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
        -ρ * (inner ℝ a x + b))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    MemLp (fun x : E => inner ℝ a x + b) 2 (gibbsMeasure volume V) := by
  exact (affine_eigenfunction_hasLaw_gaussian V hV a ha b ρ hρ heigen hprob).memLp
    IsGaussian.memLp_two_id

/-- The actual Gibbs expectation of the affine eigenfunction is zero. -/
theorem affine_eigenfunction_mean_zero
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (ha : a ≠ 0) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
        -ρ * (inner ℝ a x + b))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    ∫ x : E, (inner ℝ a x + b) ∂gibbsMeasure volume V = 0 := by
  simpa using (affine_eigenfunction_hasLaw_gaussian V hV a ha b ρ hρ heigen hprob).integral_eq

/-- The Gaussian factor computes the actual squared L² integral. -/
theorem affine_eigenfunction_second_moment
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (ha : a ≠ 0) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
        -ρ * (inner ℝ a x + b))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    ∫ x : E, (inner ℝ a x + b) ^ 2 ∂gibbsMeasure volume V = ‖a‖ ^ 2 / ρ := by
  have hg : ∫ y : ℝ, y ^ 2 ∂gaussianReal 0 (‖a‖ ^ 2 / ρ).toNNReal =
      (‖a‖ ^ 2 / ρ).toNNReal := by
    have h := variance_eq_integral (X := fun y : ℝ => y)
      (μ := gaussianReal 0 (‖a‖ ^ 2 / ρ).toNNReal) (by fun_prop)
    simpa using h.symm
  have h := (affine_eigenfunction_hasLaw_gaussian V hV a ha b ρ hρ heigen hprob).integral_comp
    (f := fun y : ℝ => y ^ 2) (by fun_prop)
  simp only [Function.comp_apply] at h
  rw [hg] at h
  simpa only [Real.toNNReal_of_nonneg (div_nonneg (sq_nonneg _) hρ.le), NNReal.coe_mk] using h

/-- The true L² element associated to the affine eigenfunction has the
gradient normalization stated in Remark 3.2. -/
theorem affine_eigenfunction_L2_gradient_norm
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (ha : a ≠ 0) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
        -ρ * (inner ℝ a x + b))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    ‖a‖ ^ 2 = ρ * ‖(affine_eigenfunction_memLp V hV a ha b ρ hρ heigen hprob).toLp
      (fun x : E => inner ℝ a x + b)‖ ^ 2 := by
  rw [norm_toLp_sq, affine_eigenfunction_second_moment V hV a ha b ρ hρ heigen hprob]
  field_simp

/-- The gradient normalization as an equality of actual pointwise gradient
norm and actual Gibbs second moment. -/
theorem affine_eigenfunction_gradient_second_moment
    (V : E → ℝ) (hV : Differentiable ℝ V) (a : E) (ha : a ≠ 0) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x : E,
      langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
        -ρ * (inner ℝ a x + b))
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (x : E) :
    ‖gradient (fun y : E => inner ℝ a y + b) x‖ ^ 2 =
      ρ * ∫ y : E, (inner ℝ a y + b) ^ 2 ∂gibbsMeasure volume V := by
  rw [gradient_inner_add_const,
    affine_eigenfunction_second_moment V hV a ha b ρ hρ heigen hprob]
  field_simp

end CutoffRigidity
