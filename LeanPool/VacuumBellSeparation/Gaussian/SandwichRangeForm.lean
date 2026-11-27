/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.UnitarySandwich

/-!
# The genuine inverse-domain sandwich form

For an injective bounded map R, its inverse is a linear map on its actual
range, not a bounded operator on the Hilbert space. If R is self-adjoint,
the bounded factorization R Θ R=A is equivalent to the literal inverse
form on that range. Density of the range gives uniqueness of the bounded
extension. These facts justify later power traces of a positive extension.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Operator inverse range obtained from `LinearMap.range`. -/
def operatorInverseRange (R : E →L[ℂ] E) := LinearMap.range R.toLinearMap

/-- Linear map for the operator inverse on range, of type `operatorInverseRange R →ₗ[ℂ] E`. -/
def operatorInverseOnRange (R : E →L[ℂ] E) (hR : Function.Injective R) :
    operatorInverseRange R →ₗ[ℂ] E :=
  (LinearEquiv.ofInjective R.toLinearMap hR).symm.toLinearMap

omit [CompleteSpace E] in
@[simp] theorem operatorInverseOnRange_apply_image (R : E →L[ℂ] E)
    (hR : Function.Injective R) (x : E) :
    operatorInverseOnRange R hR ⟨R x, ⟨x, rfl⟩⟩ = x :=
  (LinearEquiv.ofInjective R.toLinearMap hR).symm_apply_apply x

omit [CompleteSpace E] in
@[simp] theorem operator_apply_inverseOnRange (R : E →L[ℂ] E)
    (hR : Function.Injective R) (x : operatorInverseRange R) :
    R (operatorInverseOnRange R hR x) = (x : E) :=
  congrArg Subtype.val ((LinearEquiv.ofInjective R.toLinearMap hR).apply_symm_apply x)

/-- Inverse sandwich range form defined as `inner ℂ (operatorInverseOnRange R hR x) (A
(operatorInverseOnRange R hR y))`. -/
def inverseSandwichRangeForm (R : E →L[ℂ] E) (hR : Function.Injective R)
    (A : E →L[ℂ] E) (x y : operatorInverseRange R) : ℂ :=
  inner ℂ (operatorInverseOnRange R hR x) (A (operatorInverseOnRange R hR y))

theorem sandwich_factorization_iff_range_form
    (R : E →L[ℂ] E) (hR : Function.Injective R) (hs : IsSelfAdjoint R)
    (A Θ : E →L[ℂ] E) : R * Θ * R = A ↔
      ∀ x y : operatorInverseRange R,
        inner ℂ (x : E) (Θ (y : E)) = inverseSandwichRangeForm R hR A x y := by
  constructor
  · intro hf x y
    unfold inverseSandwichRangeForm
    rw [← hf]
    simp only [mul_apply_eq_comp]
    simpa only [hs.adjoint_eq, operator_apply_inverseOnRange] using
      (R.adjoint_inner_right (operatorInverseOnRange R hR x)
        (Θ (R (operatorInverseOnRange R hR y)))).symm
  · intro hf
    ext y
    apply ext_inner_left ℂ
    intro x
    have h := hf ⟨R x, ⟨x, rfl⟩⟩ ⟨R y, ⟨y, rfl⟩⟩
    simp only [inverseSandwichRangeForm, operatorInverseOnRange_apply_image] at h
    change inner ℂ x (R (Θ (R y))) = inner ℂ x (A y)
    calc
      _ = inner ℂ (R x) (Θ (R y)) := by
        simpa only [hs.adjoint_eq] using R.adjoint_inner_right x (Θ (R y))
      _ = _ := h

omit [CompleteSpace E] in
theorem sandwich_factorization_unique (R : E →L[ℂ] E)
    (hinj : Function.Injective R) (hdense : DenseRange R)
    {Θ Ξ : E →L[ℂ] E} (h : R * Θ * R = R * Ξ * R) : Θ = Ξ := by
  have hcomp : (fun x => Θ (R x)) = fun x => Ξ (R x) := by
    funext x
    apply hinj
    simpa only [mul_apply_eq_comp] using DFunLike.congr_fun h x
  exact DFunLike.coe_injective (hdense.equalizer Θ.continuous Ξ.continuous hcomp)

end VacuumBellSeparation.Gaussian
