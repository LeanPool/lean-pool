/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HilbertComplexification
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Bounded operator equality from the dense original real tests

The complex span is derived from the literal real and imaginary coordinates.
No complex density or complexified physical injectivity is an assumption.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open HilbertComplexification

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {α β : Type*}

theorem complexification_operator_ext_real
    {A B : HilbertComplexification E →L[ℂ] HilbertComplexification F}
    (h : ∀ x : E, ∀ y : F, inner ℂ (ofReal y) (A (ofReal x)) =
      inner ℂ (ofReal y) (B (ofReal x))) : A = B := by
  have hr (x : E) : A (ofReal x) = B (ofReal x) := by
    apply ext_inner_left ℂ
    intro z
    rw [eq_ofReal_add_I_smul z, inner_add_left, inner_add_left,
      inner_smul_left, inner_smul_left, h x z.re, h x z.im]
  apply ContinuousLinearMap.ext
  intro z
  rw [eq_ofReal_add_I_smul z, map_add, map_add, map_smul, map_smul, hr, hr]

theorem complexification_operator_ext_dense_real
    {e : α → E} {f : β → F} (he : DenseRange e) (hf : DenseRange f)
    {A B : HilbertComplexification E →L[ℂ] HilbertComplexification F}
    (h : ∀ x : α, ∀ y : β, inner ℂ (ofReal (f y)) (A (ofReal (e x))) =
      inner ℂ (ofReal (f y)) (B (ofReal (e x)))) : A = B := by
  apply complexification_operator_ext_real
  have hy (x : α) (y : F) : inner ℂ (ofReal y) (A (ofReal (e x))) =
      inner ℂ (ofReal y) (B (ofReal (e x))) := by
    exact congrFun (hf.equalizer
      ((ofReal.continuous).inner continuous_const)
      ((ofReal.continuous).inner continuous_const) (funext (fun y => h x y))) y
  intro x y
  exact congrFun (he.equalizer
    (continuous_const.inner (A.continuous.comp ofReal.continuous))
    (continuous_const.inner (B.continuous.comp ofReal.continuous)) (funext (fun u => hy u y))) x

end VacuumBellSeparation.Gaussian
