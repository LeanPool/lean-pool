/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Riesz representation of bounded distributions on a dense test domain

A norm bound on an actual linear functional over a dense Hilbert subspace
produces an actual Hilbert vector with the same bound. This is used to
construct weak L² derivatives from bounds proved on compact tests.
-/

public section

namespace CutoffRigidity

/-- Bounded linear distributions on a genuine dense Hilbert test subspace
have actual Riesz representatives, with the proved bound retained. -/
theorem exists_riesz_of_dense_submodule_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (D : Submodule ℝ H) (hD : Dense (D : Set H)) (ell : D →ₗ[ℝ] ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v : D, |ell v| ≤ C * ‖(v : H)‖) :
    ∃ h : H, ‖h‖ ≤ C ∧ ∀ v : D, ell v = inner ℝ h (v : H) := by
  let L : H →L[ℝ] ℝ := ell.extendOfNorm D.subtype
  have hb : ∀ v : D, ‖ell v‖ ≤ C * ‖D.subtype v‖ := by
    intro v
    exact hbound v
  have hL : ‖L‖ ≤ C := LinearMap.opNorm_extendOfNorm_le hD.denseRange_val hC hb
  let h := (InnerProductSpace.toDual ℝ H).symm L
  refine ⟨h, ?_, ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ H).symm L‖ ≤ C
    rw [LinearIsometryEquiv.norm_map]
    exact hL
  · intro v
    rw [InnerProductSpace.toDual_symm_apply]
    exact (LinearMap.extendOfNorm_eq hD.denseRange_val ⟨C, hb⟩ v).symm

end CutoffRigidity
