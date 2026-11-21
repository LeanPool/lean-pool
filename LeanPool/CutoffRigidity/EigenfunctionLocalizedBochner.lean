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
