/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Bounded factorization through an injective operator with dense range

A norm bound in the range norm defines a bounded map there and its unique
continuous extension. The inverse of the injective operator is never assumed
bounded. The codomain may be any complete complex normed space.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem existsUnique_factor_of_denseRange_bound (A : E →L[ℂ] E)
    (hA : Function.Injective A) (hd : DenseRange A) (T : E →ₗ[ℂ] F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖T z‖ ≤ C * ‖A z‖) :
    ∃! L : E →L[ℂ] F, (∀ z, L (A z) = T z) ∧ ‖L‖ ≤ C := by
  let e := LinearEquiv.ofInjective A.toLinearMap hA
  let l : A.range →ₗ[ℂ] F := T.comp e.symm.toLinearMap
  have hl (z : E) : l (e z) = T z := by
    change T (e.symm (e z)) = T z
    rw [LinearEquiv.symm_apply_apply]
  have hbl : ∀ y : A.range, ‖l y‖ ≤ C * ‖y‖ := by
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    exact (show ‖l (e z)‖ ≤ C * ‖A z‖ by rw [hl]; exact hb z)
  let lc : A.range →L[ℂ] F := l.mkContinuous C hbl
  let L : E →L[ℂ] F := lc.extend A.range.subtypeL
  have hdom : Dense (A.range : Set E) := hd
  have hext (z : E) : L (A z) = T z := by
    have hh := lc.extend_eq (e := A.range.subtypeL) hdom.denseRange_val
      isUniformEmbedding_subtype_val.isUniformInducing (e z)
    exact hh.trans (hl z)
  have hbound (x : E) : ‖L x‖ ≤ C * ‖x‖ := by
    refine hd.induction_on (p := fun y => ‖L y‖ ≤ C * ‖y‖) x
      (isClosed_le L.continuous.norm (continuous_const.mul continuous_norm)) ?_
    intro z
    rw [hext]
    exact hb z
  refine ⟨L, ⟨hext, L.opNorm_le_bound hC hbound⟩, ?_⟩
  intro Q hQ
  apply ContinuousLinearMap.coeFn_injective
  exact hd.equalizer Q.continuous L.continuous (funext fun z => (hQ.1 z).trans (hext z).symm)

omit [CompleteSpace F] in
/-- A bounded factorization gives the original range-norm inequality. -/
theorem bound_of_factor (A : E →L[ℂ] E) (T : E →ₗ[ℂ] F)
    (L : E →L[ℂ] F) (hL : ∀ z, L (A z) = T z) {C : ℝ} (hC : ‖L‖ ≤ C) :
    ∀ z, ‖T z‖ ≤ C * ‖A z‖ := by
  intro z
  rw [← hL z]
  exact (L.le_opNorm (A z)).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

end VacuumBellSeparation
