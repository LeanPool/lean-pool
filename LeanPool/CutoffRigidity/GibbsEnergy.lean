/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsIntegrationByParts
public import LeanPool.CutoffRigidity.ConvexInteraction

/-!
# The Gibbs Dirichlet form and eigenfunction energy identity

This file derives the paper's identity `∫ f Lg = -∫ ⟪∇f,∇g⟫` by applying
the proved weighted directional integration by parts in each actual Euclidean
coordinate. The resulting energy identity for pointwise eigenfunctions is
then obtained by substitution, as in Remark `rem_eigen_grad`.

All product-integrability assumptions are explicit. Extending the identity
to the full self-adjoint generator domain, and proving that the paper's
spectral eigenfunctions satisfy these assumptions, remain separate tasks.
-/

public section

open MeasureTheory

namespace CutoffRigidity

/-- The actual derivative in a standard coordinate direction is the matching
coordinate of the actual Euclidean gradient. -/
theorem fderiv_single_eq_gradient_coordinate {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    fderiv ℝ f x (EuclideanSpace.single i 1) = gradient f x i := by
  rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

/-- The Euclidean gradient inner product is the sum of actual coordinate
Fréchet derivative products. -/
theorem inner_gradient_eq_sum_fderiv_single {d : ℕ}
    (f g : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (gradient f x) (gradient g x) =
      ∑ i : Fin d, fderiv ℝ f x (EuclideanSpace.single i 1) *
        fderiv ℝ g x (EuclideanSpace.single i 1) := by
  simp_rw [fderiv_single_eq_gradient_coordinate]
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]

/-- Weighted integration by parts applied to one directional derivative of g;
the potential drift cancels its density derivative term. -/
theorem integral_mul_second_fderiv_gibbs_sub_eq_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : Measure E) [m.IsAddHaarMeasure]
    {V f g : E → ℝ} (hV : Differentiable ℝ V) (hf : Differentiable ℝ f)
    (hg' : Differentiable ℝ (fderiv ℝ g)) (v : E)
    (hfDg : Integrable (fun x => f x * fderiv ℝ g x v) (gibbsMeasure m V))
    (hfDDg : Integrable (fun x => f x * fderiv ℝ (fun y => fderiv ℝ g y v) x v)
      (gibbsMeasure m V))
    (hDfDg : Integrable (fun x => fderiv ℝ f x v * fderiv ℝ g x v) (gibbsMeasure m V))
    (hfDVDg : Integrable (fun x => f x * fderiv ℝ V x v * fderiv ℝ g x v)
      (gibbsMeasure m V)) :
    (∫ x, f x * (fderiv ℝ (fun y => fderiv ℝ g y v) x v -
      fderiv ℝ V x v * fderiv ℝ g x v) ∂gibbsMeasure m V) =
      -(∫ x, fderiv ℝ f x v * fderiv ℝ g x v ∂gibbsMeasure m V) := by
  have hDg : Differentiable ℝ (fun x => fderiv ℝ g x v) :=
    hg'.clm_apply (differentiable_const v)
  have hdfg : Integrable
      (fun x => (fderiv ℝ f x v - f x * fderiv ℝ V x v) * fderiv ℝ g x v)
      (gibbsMeasure m V) := by
    convert hDfDg.sub hfDVDg using 1
    funext x
    dsimp only [Pi.sub_apply]
    ring
  have hibp := integral_mul_fderiv_gibbs_eq_neg m hV hf hDg v hfDg hfDDg hdfg
  have hleft : (fun x => f x * (fderiv ℝ (fun y => fderiv ℝ g y v) x v -
      fderiv ℝ V x v * fderiv ℝ g x v)) =
      fun x => f x * fderiv ℝ (fun y => fderiv ℝ g y v) x v -
        f x * fderiv ℝ V x v * fderiv ℝ g x v := by
    funext x
    ring
  have hright : (fun x => (fderiv ℝ f x v - f x * fderiv ℝ V x v) * fderiv ℝ g x v) =
      fun x => fderiv ℝ f x v * fderiv ℝ g x v -
        f x * fderiv ℝ V x v * fderiv ℝ g x v := by
    funext x
    ring
  rw [hright, integral_sub hDfDg hfDVDg] at hibp
  rw [hleft, integral_sub hfDDg hfDVDg, hibp]
  ring

/-- The Langevin differential expression is symmetric against the Gibbs
measure on the explicitly integrable domain below. -/
theorem integral_mul_langevin_eq_neg_gradient_inner {d : ℕ}
    {V f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hV : Differentiable ℝ V) (hf : Differentiable ℝ f) (hg : ContDiff ℝ 2 g)
    (hfDg : ∀ i : Fin d, Integrable
      (fun x => f x * fderiv ℝ g x (EuclideanSpace.single i 1))
      (gibbsMeasure volume V))
    (hfDDg : ∀ i : Fin d, Integrable
      (fun x => f x * fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) (gibbsMeasure volume V))
    (hDfDg : ∀ i : Fin d, Integrable
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1) *
        fderiv ℝ g x (EuclideanSpace.single i 1)) (gibbsMeasure volume V))
    (hfDVDg : ∀ i : Fin d, Integrable
      (fun x => f x * fderiv ℝ V x (EuclideanSpace.single i 1) *
        fderiv ℝ g x (EuclideanSpace.single i 1)) (gibbsMeasure volume V)) :
    (∫ x, f x * langevinDifferentialOperator V g x ∂gibbsMeasure volume V) =
      -(∫ x, inner ℝ (gradient f x) (gradient g x) ∂gibbsMeasure volume V) := by
  have hg' : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hpoint (x : EuclideanSpace ℝ (Fin d)) :
      f x * langevinDifferentialOperator V g x =
      ∑ i : Fin d, f x * (fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) - fderiv ℝ V x (EuclideanSpace.single i 1) *
          fderiv ℝ g x (EuclideanSpace.single i 1)) := by
    rw [langevinDifferentialOperator, euclideanLaplacian,
      inner_gradient_eq_sum_fderiv_single, ← Finset.sum_sub_distrib, Finset.mul_sum]
  have hcoordInt (i : Fin d) : Integrable
      (fun x => f x * (fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) - fderiv ℝ V x (EuclideanSpace.single i 1) *
          fderiv ℝ g x (EuclideanSpace.single i 1))) (gibbsMeasure volume V) := by
    convert (hfDDg i).sub (hfDVDg i) using 1
    funext x
    dsimp only [Pi.sub_apply]
    ring
  simp_rw [hpoint, inner_gradient_eq_sum_fderiv_single]
  rw [integral_finsetSum _ (fun i _ => hcoordInt i),
    integral_finsetSum _ (fun i _ => hDfDg i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_mul_second_fderiv_gibbs_sub_eq_neg volume hV hf hg'
    (EuclideanSpace.single i 1) (hfDg i) (hfDDg i) (hDfDg i) (hfDVDg i)

/-- The eigenfunction energy identity in Remark `rem_eigen_grad`, for an
actual pointwise eigenfunction satisfying the stated integration domain.
No spectral-gap or `L²` generator-domain membership is inferred here. -/
theorem integral_gradient_norm_sq_eq_rate_integral_sq {d : ℕ}
    {V f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hV : Differentiable ℝ V) (hf : ContDiff ℝ 2 f) (rate : ℝ)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -rate * f x)
    (hfDf : ∀ i : Fin d, Integrable
      (fun x => f x * fderiv ℝ f x (EuclideanSpace.single i 1))
      (gibbsMeasure volume V))
    (hfDDf : ∀ i : Fin d, Integrable
      (fun x => f x * fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) (gibbsMeasure volume V))
    (hDfDf : ∀ i : Fin d, Integrable
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1) *
        fderiv ℝ f x (EuclideanSpace.single i 1)) (gibbsMeasure volume V))
    (hfDVDf : ∀ i : Fin d, Integrable
      (fun x => f x * fderiv ℝ V x (EuclideanSpace.single i 1) *
        fderiv ℝ f x (EuclideanSpace.single i 1)) (gibbsMeasure volume V)) :
    (∫ x, ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) =
      rate * (∫ x, f x ^ 2 ∂gibbsMeasure volume V) := by
  have h := integral_mul_langevin_eq_neg_gradient_inner hV
    (hf.differentiable (by norm_num)) hf hfDf hfDDf hDfDf hfDVDf
  have hprod : (fun x => f x * langevinDifferentialOperator V f x) =
      fun x => -rate * f x ^ 2 := by
    funext x
    rw [heigen]
    ring
  rw [hprod, integral_const_mul] at h
  simp_rw [real_inner_self_eq_norm_sq] at h
  linarith

end CutoffRigidity
