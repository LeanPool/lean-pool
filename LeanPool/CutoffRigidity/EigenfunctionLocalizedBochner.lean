/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EigenfunctionCaccioppoli

/-!
# Local identities for Bochner estimates

This file supplies compact cutoff integrability, the localized Gibbs energy
identity, and the coordinate identities used by the C² rigidity proof.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A compact scalar cutoff makes every continuous product Gibbs integrable. -/
theorem integrable_cutoff_mul_continuous {V χ g : E → ℝ}
    (hV : Continuous V) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hg : Continuous g) :
    Integrable (fun x => χ x * g x) (gibbsMeasure volume V) := by
  apply integrable_gibbs_of_continuous_hasCompactSupport hV (hχ.mul hg)
  simpa only [Pi.mul_def] using hχc.mul_right (f' := g)

/-- The squared-cutoff version used in the local energy identity. -/
theorem integrable_cutoff_square_mul_continuous {V χ g : E → ℝ}
    (hV : Continuous V) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hg : Continuous g) :
    Integrable (fun x => χ x ^ 2 * g x) (gibbsMeasure volume V) := by
  have hcs : HasCompactSupport (fun x => χ x ^ 2) := by
    simpa only [Function.comp_def] using hχc.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  exact integrable_cutoff_mul_continuous hV (hχ.pow 2) hcs hg

/-- The actual pointwise generator sends C² functions to continuous functions. -/
theorem continuous_langevinDifferentialOperator {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) :
    Continuous (langevinDifferentialOperator V f) := by
  have hd1 (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hd2 (i : Fin d) : Continuous (coordinateDerivative i (coordinateDerivative i f)) := by
    have h : ContDiff ℝ 0 (coordinateDerivative i (coordinateDerivative i f)) := by
      apply contDiff_coordinateDerivative
      convert hd1 i using 1
      norm_num
    exact h.continuous
  have hLap : Continuous (euclideanLaplacian f) := by
    change Continuous (fun x => ∑ i : Fin d, coordinateDerivative i (coordinateDerivative i f) x)
    fun_prop
  exact hLap.sub (((differentiable_gradient_of_contDiff_two hV).continuous).inner
    ((differentiable_gradient_of_contDiff_two hf).continuous))

/-- The exact local energy identity for an arbitrary C² function, with the
actual compact test `χ²f`; no eigenfunction or global-domain premise. -/
theorem cutoff_gibbs_energy_identity {V f χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) :
    (∫ x, χ x ^ 2 * f x * langevinDifferentialOperator V f x ∂gibbsMeasure volume V) +
      (∫ x, χ x ^ 2 * ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) +
        2 * (∫ x, χ x * f x * inner ℝ (gradient χ x) (gradient f x) ∂gibbsMeasure volume V) = 0
          := by
  have htest : ContDiff ℝ 1 (fun x => χ x ^ 2 * f x) :=
    ((hχ.pow 2).mul hf).of_le (by norm_num)
  have htestc : HasCompactSupport (fun x => χ x ^ 2 * f x) := by
    have hcs : HasCompactSupport (fun x => χ x ^ 2) := by
      simpa only [Function.comp_def] using hχc.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
    simpa only [Pi.mul_def] using hcs.mul_right (f' := f)
  have hGf : Continuous (gradient f) := (differentiable_gradient_of_contDiff_two hf).continuous
  have hGχ : Continuous (gradient χ) := (differentiable_gradient_of_contDiff_two hχ).continuous
  have hA : Integrable (fun x => χ x ^ 2 * ‖gradient f x‖ ^ 2) (gibbsMeasure volume V) :=
    integrable_cutoff_square_mul_continuous hV.continuous hχ.continuous hχc (by fun_prop)
  have hC : Integrable (fun x => χ x * f x * inner ℝ (gradient χ x) (gradient f x))
      (gibbsMeasure volume V) := by
    have h := integrable_cutoff_mul_continuous hV.continuous hχ.continuous hχc
      (hf.continuous.mul (hGχ.inner hGf))
    simpa only [mul_assoc, Pi.mul_apply] using h
  have h := compact_test_gibbs_energy hV htest hf htestc
  have hright (x : E) : inner ℝ (gradient (fun y => χ y ^ 2 * f y) x) (gradient f x) =
      χ x ^ 2 * ‖gradient f x‖ ^ 2 +
        2 * (χ x * f x * inner ℝ (gradient χ x) (gradient f x)) := by
    rw [gradient_cutoff_square_mul (hχ.differentiable (by norm_num)) (hf.differentiable
      (by norm_num)),
      inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  simp_rw [hright] at h
  rw [integral_add hA (hC.const_mul 2), integral_const_mul] at h
  linarith

/-- Differentiating an actual pointwise eigenfunction equation, using the
proved commutator rather than assuming a vector eigenfunction equation. -/
theorem langevin_coordinate_eigenfunction_equation {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (ρ : ℝ)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x)
    (i : Fin d) (x : E) :
    langevinDifferentialOperator V (coordinateDerivative i f) x =
      -ρ * coordinateDerivative i f x +
        ∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f
          x := by
  have hder : coordinateDerivative i (langevinDifferentialOperator V f) x =
      -ρ * coordinateDerivative i f x := by
    unfold coordinateDerivative
    rw [funext heigen, fderiv_const_mul ((hf.differentiable (by norm_num)) x), smul_apply,
      smul_eq_mul]
  have h := coordinateDerivative_langevin_commutator hV hf i x
  linarith

/-- Parseval's formula for the actual coordinate derivatives. -/
theorem sum_coordinateDerivative_sq (f : E → ℝ) (x : E) :
    (∑ i : Fin d, (coordinateDerivative i f x) ^ 2) = ‖gradient f x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coordinateDerivative, fderiv_single_eq_gradient_coordinate]

/-- The potential term in the localized identity is the actual Hessian
quadratic form with the cutoff weight. -/
theorem cutoff_hessian_coordinate_contraction {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (f χ : E → ℝ) (x : E) :
    (∑ i : Fin d, χ x ^ 2 * coordinateDerivative i f x *
      (∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f
        x)) =
      χ x ^ 2 * fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x) := by
  rw [hessian_gradient_coordinate_contraction hV f]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end CutoffRigidity
