/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.HilbertComplexification

/-!
# The actual complex-linear extension of a real-linear functional
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open HilbertComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Extend a real-linear functional to the canonical complexification of its source. -/
noncomputable def complexifyFunctional (L : E →ₗ[ℝ] ℂ) :
    HilbertComplexification E →ₗ[ℂ] ℂ where
  toFun z := L z.re + Complex.I * L z.im
  map_add' z w := by simp only [re_add, im_add, map_add]; ring
  map_smul' c z := by
    simp only [re_smul, im_smul, map_sub, map_add, map_smul, Complex.real_smul,
      smul_eq_mul, RingHom.id_apply]
    conv_rhs => rw [← Complex.re_add_im c]
    ring_nf
    rw [Complex.I_sq]
    ring

@[simp]
theorem complexifyFunctional_mk (L : E →ₗ[ℝ] ℂ) (x y : E) :
    complexifyFunctional L (mk x y) = L x + Complex.I * L y := rfl

@[simp]
theorem complexifyFunctional_ofReal (L : E →ₗ[ℝ] ℂ) (x : E) :
    complexifyFunctional L (ofReal x) = L x := by
  simp only [complexifyFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    ofReal_re, ofReal_im, map_zero, mul_zero, add_zero]

end VacuumBellSeparation.Gaussian
