/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeGeometry
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# The true Euclidean operator norm and containing transformed wedges

The physical spacetime carrier has the product maximum norm. Conjugating
through WithLp 2 gives its genuine Euclidean four-norm and the operator
norm used in Section 5.1, with the manuscript's square-root-two constant.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Euclidean spacetime with underlying type `WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3))`. -/
abbrev EuclideanSpacetime := WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3))

/-- Identify spacetime with the Euclidean product of the time axis and three spatial coordinates. -/
noncomputable def spacetimeEuclideanEquiv : Spacetime ≃L[ℝ] EuclideanSpacetime :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (EuclideanSpace ℝ (Fin 3))).symm

theorem norm_spacetimeEuclideanEquiv (x : Spacetime) :
    ‖spacetimeEuclideanEquiv x‖ = spacetimeEuclideanNorm x := by
  rw [WithLp.prod_norm_eq_of_L2]
  change Real.sqrt (‖x.1‖ ^ 2 + ‖x.2‖ ^ 2) = _
  rw [Real.norm_eq_abs, sq_abs]
  rfl

/-- Euclidean spacetime map obtained from `spacetimeEuclideanEquiv.symm.trans`. -/
noncomputable def euclideanSpacetimeMap (Λ : Spacetime ≃L[ℝ] Spacetime) :
    EuclideanSpacetime ≃L[ℝ] EuclideanSpacetime :=
  spacetimeEuclideanEquiv.symm.trans (Λ.trans spacetimeEuclideanEquiv)

/-- Spacetime Euclidean operator norm. -/
noncomputable def spacetimeEuclideanOperatorNorm (Λ : Spacetime ≃L[ℝ] Spacetime) : ℝ :=
  ‖(euclideanSpacetimeMap Λ).toContinuousLinearMap‖

theorem spacetimeEuclideanOperatorNorm_nonneg (Λ : Spacetime ≃L[ℝ] Spacetime) :
    0 ≤ spacetimeEuclideanOperatorNorm Λ := norm_nonneg _

theorem spacetimeEuclideanNorm_map_le (Λ : Spacetime ≃L[ℝ] Spacetime) (x : Spacetime) :
    spacetimeEuclideanNorm (Λ x) ≤ spacetimeEuclideanOperatorNorm Λ * spacetimeEuclideanNorm x := by
  have h := (euclideanSpacetimeMap Λ).toContinuousLinearMap.le_opNorm
    (spacetimeEuclideanEquiv x)
  simpa only [euclideanSpacetimeMap, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    norm_spacetimeEuclideanEquiv, spacetimeEuclideanOperatorNorm] using h

/-- Exact containing geometry for an arbitrary invertible real spacetime map. -/
theorem doubleCone_subset_transformed_leftWedge
    (Λ : Spacetime ≃L[ℝ] Spacetime) {R ℓ : ℝ} (hR : 0 < R)
    (hℓ : Real.sqrt 2 * spacetimeEuclideanOperatorNorm Λ.symm < ℓ) :
    doubleCone 0 R ⊆ Λ '' leftWedge (ℓ * R) := by
  intro x hx
  refine ⟨Λ.symm x, ?_, Λ.apply_symm_apply x⟩
  apply mem_leftWedge_of_euclidean_bound
    ((spacetimeEuclideanNorm_map_le Λ.symm x).trans
      (mul_le_mul_of_nonneg_left (spacetimeEuclideanNorm_lt_of_mem_doubleCone hx).le
        (spacetimeEuclideanOperatorNorm_nonneg Λ.symm)))
  simpa only [mul_assoc] using mul_lt_mul_of_pos_right hℓ hR

end VacuumBellSeparation
