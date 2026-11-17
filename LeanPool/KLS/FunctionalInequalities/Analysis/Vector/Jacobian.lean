/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # The coarea Jacobian of a linear map

The scalar weighted coarea formula proved in `Analysis/Coarea/` integrates `‖gradient u x‖` against
Lebesgue measure and slices along the fibres of `u : V → ℝ`.  For a map into an `m`-dimensional
target the corresponding density is the **coarea Jacobian**

`coareaJacobian L = sqrt (det (L ∘ Lᵀ))`,

with `Lᵀ` the adjoint, so that `L ∘ Lᵀ : W → W` is a genuine `m × m` determinant.  This module is
the linear-algebra layer of the codimension-`m` coarea program; it proves no coarea formula.

Mathlib already carries the rectangular volume factor `LinearMap.normDet f = sqrt (det (fᵀ ∘ f))`,
which is the **area**-formula Jacobian of a map out of a finite-dimensional space.  The coarea
Jacobian is its adjoint counterpart, `coareaJacobian L = normDet Lᵀ`, and that is how it is defined
here rather than by re-deriving the determinant theory.

The point of the module is the compatibility with everything already proved: `coareaJacobian` of a
real-valued differential is exactly `‖gradient u x‖` (`coareaJacobian_fderiv`), so the scalar
theory is literally the `m = 1` case of this density and nothing already certified has to change.
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The **coarea Jacobian** `sqrt (det (L ∘ Lᵀ))` of a linear map, the codimension-`m` density of
the coarea formula.  It is defined as Mathlib's rectangular volume factor of the adjoint; the
defining identity is `coareaJacobian_sq`. -/
def coareaJacobian (L : V →L[ℝ] W) : ℝ :=
  LinearMap.normDet (LinearMap.adjoint (L : V →ₗ[ℝ] W))

theorem coareaJacobian_nonneg (L : V →L[ℝ] W) : 0 ≤ coareaJacobian L :=
  LinearMap.normDet_nonneg _

/-- The defining identity: the square of the coarea Jacobian is `det (L ∘ Lᵀ)`, a determinant on
the **target**, so it is the `m × m` Gram determinant and not the `n × n` one. -/
theorem coareaJacobian_sq (L : V →L[ℝ] W) :
    coareaJacobian L ^ 2 =
      LinearMap.det ((L : V →ₗ[ℝ] W) ∘ₗ LinearMap.adjoint (L : V →ₗ[ℝ] W)) := by
  have h := LinearMap.normDet_sq (LinearMap.adjoint (L : V →ₗ[ℝ] W))
  rw [LinearMap.adjoint_adjoint] at h
  exact_mod_cast h

/-! ### The scalar case is the gradient -/

/-- For a real-valued functional the adjoint sends `1` to the Riesz representative. -/
theorem adjoint_one (L : V →L[ℝ] ℝ) :
    LinearMap.adjoint (L : V →ₗ[ℝ] ℝ) 1 = (InnerProductSpace.toDual ℝ V).symm L := by
  refine ext_inner_right ℝ fun v => ?_
  rw [LinearMap.adjoint_inner_left, InnerProductSpace.toDual_symm_apply]
  simp

/-- The coarea Jacobian of a real-valued functional is the norm of its Riesz representative. -/
theorem coareaJacobian_eq_norm_toDual_symm (L : V →L[ℝ] ℝ) :
    coareaJacobian L = ‖(InnerProductSpace.toDual ℝ V).symm L‖ := by
  have key : ⟪(InnerProductSpace.toDual ℝ V).symm L, (InnerProductSpace.toDual ℝ V).symm L⟫
      = L ((InnerProductSpace.toDual ℝ V).symm L) := InnerProductSpace.toDual_symm_apply
  have hval : ((L : V →ₗ[ℝ] ℝ) ∘ₗ LinearMap.adjoint (L : V →ₗ[ℝ] ℝ)) 1
      = ‖(InnerProductSpace.toDual ℝ V).symm L‖ ^ 2 := by
    simp only [LinearMap.comp_apply, adjoint_one L, ContinuousLinearMap.coe_coe]
    rw [← real_inner_self_eq_norm_sq, key]
  have ha : 0 ≤ coareaJacobian L := coareaJacobian_nonneg L
  have hb : 0 ≤ ‖(InnerProductSpace.toDual ℝ V).symm L‖ := norm_nonneg _
  have h : coareaJacobian L ^ 2 = ‖(InnerProductSpace.toDual ℝ V).symm L‖ ^ 2 := by
    rw [coareaJacobian_sq, LinearMap.det_ring, hval]
  nlinarith [sq_nonneg (coareaJacobian L - ‖(InnerProductSpace.toDual ℝ V).symm L‖),
    sq_nonneg (coareaJacobian L + ‖(InnerProductSpace.toDual ℝ V).symm L‖)]

/-- **Compatibility with the proved scalar theory**: the coarea Jacobian of the differential of a
real-valued function is exactly the norm of its gradient, the integrand of the weighted coarea
formula C¹ coarea/globally Lipschitz coarea/locally Lipschitz coarea. -/
theorem coareaJacobian_fderiv (u : V → ℝ) (x : V) :
    coareaJacobian (fderiv ℝ u x) = ‖gradient u x‖ := by
  rw [coareaJacobian_eq_norm_toDual_symm]
  rfl

/-! ### The regular set -/

/-- The kernel of the adjoint is the orthogonal complement of the range. -/
theorem ker_adjoint (L : V →L[ℝ] W) :
    LinearMap.ker (LinearMap.adjoint (L : V →ₗ[ℝ] W)) = (LinearMap.range (L : V →ₗ[ℝ] W))ᗮ := by
  ext w
  simp only [LinearMap.mem_ker, Submodule.mem_orthogonal, LinearMap.mem_range]
  constructor
  · rintro hw _ ⟨v, rfl⟩
    rw [real_inner_comm, ← LinearMap.adjoint_inner_left, hw, inner_zero_left]
  · intro hw
    refine ext_inner_right ℝ fun v => ?_
    rw [LinearMap.adjoint_inner_left, inner_zero_left]
    exact (real_inner_comm _ _).trans (hw _ ⟨v, rfl⟩)

/-- **The regular set**: the coarea Jacobian vanishes exactly where the differential fails to be
surjective.  This is the characterization the codimension-`m` coarea formula splits on, and for
`W = ℝ` it is `‖gradient u x‖ = 0 ↔ fderiv ℝ u x = 0`. -/
theorem coareaJacobian_eq_zero_iff (L : V →L[ℝ] W) :
    coareaJacobian L = 0 ↔ ¬ Function.Surjective (L : V →ₗ[ℝ] W) := by
  rw [coareaJacobian, LinearMap.normDet_eq_zero_iff_ker_ne_bot, ker_adjoint]
  exact not_congr ((Submodule.orthogonal_eq_bot_iff
    (K := LinearMap.range (L : V →ₗ[ℝ] W))).trans LinearMap.range_eq_top)

theorem coareaJacobian_ne_zero_iff (L : V →L[ℝ] W) :
    coareaJacobian L ≠ 0 ↔ Function.Surjective (L : V →ₗ[ℝ] W) := by
  rw [Ne, coareaJacobian_eq_zero_iff, not_not]

end FunctionalInequalities.Analysis
