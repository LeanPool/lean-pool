/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Dense range and injectivity for Hilbert-space operators -/

public section

namespace CutoffRigidity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An injective symmetric bounded operator on a real Hilbert space has dense range. -/
theorem denseRange_of_injective_symmetric (R : H →L[ℝ] H) (hR : Function.Injective R)
    (hsym : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) : DenseRange R := by
  change Dense (R.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hzero : R x = 0 := by
    apply ext_inner_right ℝ
    intro y
    rw [hsym]
    have hxy := ((R.range.mem_orthogonal x).mp hx) (R y) ⟨y, rfl⟩
    simpa only [inner_zero_left, real_inner_comm] using hxy
  exact hR (by simpa only [map_zero] using hzero)

/-- The product of a densely ranged operator with its adjoint is injective. -/
theorem self_comp_adjoint_injective_of_denseRange {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] (J : K →L[ℝ] H) (hJ : DenseRange J) :
    Function.Injective (J.comp J.adjoint) := by
  apply J.self_comp_adjoint_injective_iff.mpr
  intro f g h
  apply hJ.eq_of_inner_left ℝ
  intro u
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_left, h]

end CutoffRigidity
