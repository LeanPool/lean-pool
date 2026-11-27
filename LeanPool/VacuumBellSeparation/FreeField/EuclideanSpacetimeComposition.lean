/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.EuclideanWedgeContainment
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Composition and continuity of the genuine Euclidean spacetime norm

All operator norms act on the actual WithLp 2 four-space. Finite
dimensional pointwise continuity is sufficient for operator-norm
continuity, as required for compact Lorentz parameter families.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem euclideanSpacetimeMap_trans_clm (Λ Γ : Spacetime ≃L[ℝ] Spacetime) :
    (euclideanSpacetimeMap (Λ.trans Γ)).toContinuousLinearMap =
      (euclideanSpacetimeMap Γ).toContinuousLinearMap.comp
        (euclideanSpacetimeMap Λ).toContinuousLinearMap := by
  ext x
  simp only [euclideanSpacetimeMap, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]

theorem spacetimeEuclideanOperatorNorm_trans_le (Λ Γ : Spacetime ≃L[ℝ] Spacetime) :
    spacetimeEuclideanOperatorNorm (Λ.trans Γ) ≤
      spacetimeEuclideanOperatorNorm Γ * spacetimeEuclideanOperatorNorm Λ := by
  unfold spacetimeEuclideanOperatorNorm
  rw [euclideanSpacetimeMap_trans_clm]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem continuous_spacetimeEuclideanOperatorNorm_family
    {A : Type*} [TopologicalSpace A] (Λ : A → Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ x : Spacetime, Continuous fun a => Λ a x) :
    Continuous (fun a => spacetimeEuclideanOperatorNorm (Λ a)) := by
  have h : Continuous (fun a => (euclideanSpacetimeMap (Λ a)).toContinuousLinearMap) := by
    apply continuous_clm_apply.mpr
    intro x
    exact spacetimeEuclideanEquiv.continuous.comp (hΛ (spacetimeEuclideanEquiv.symm x))
  exact h.norm

end VacuumBellSeparation
