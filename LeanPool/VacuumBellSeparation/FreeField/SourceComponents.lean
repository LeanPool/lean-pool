/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceSpace
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# The two components of the completed source space

The literal maps `(f,g) ↦ (f,0)` and `(f,g) ↦ (0,g)` preserve support.
Their boundedness follows from the actual diagonal covariance, so their
extensions are defined on the actual source completion. The completed norm
retains the Pythagorean decomposition. No distributional support or Sobolev
identification is inferred merely from these projection identities.
-/

@[expose] public section

open scoped InnerProductSpace

namespace VacuumBellSeparation

@[simp] theorem spatialFourier_zero (p : EuclideanSpace ℝ (Fin 3)) :
    spatialFourier 0 p = 0 := by
  change (∫ x, Complex.exp (-(Complex.I * ↑(inner ℝ p x))) * (0 : ℂ)) = 0
  simp

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- First literal source component, with unchanged localization. -/
def sourceTestFirst : SourceTestSpace hm U →ₗ[ℝ] SourceTestSpace hm U where
  toFun u := ⟨(u.1.1, 0), u.2.1, by
    change tsupport (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ⊆ U
    simp⟩
  map_add' u v := by
    apply Subtype.ext
    change (u.1.1 + v.1.1, 0) = (u.1.1 + v.1.1, 0 + 0)
    simp
  map_smul' a u := by
    apply Subtype.ext
    change (a • u.1.1, 0) = (a • u.1.1, a • (0 : SpatialTestFunction))
    simp

/-- Second literal source component, with unchanged localization. -/
def sourceTestSecond : SourceTestSpace hm U →ₗ[ℝ] SourceTestSpace hm U where
  toFun u := ⟨(0, u.1.2), by
    change tsupport (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ⊆ U
    simp, u.2.2⟩
  map_add' u v := by
    apply Subtype.ext
    change (0, u.1.2 + v.1.2) = (0 + 0, u.1.2 + v.1.2)
    simp
  map_smul' a u := by
    apply Subtype.ext
    change (0, a • u.1.2) = (a • (0 : SpatialTestFunction), a • u.1.2)
    simp

@[simp] theorem sourceTestFirst_val (u : SourceTestSpace hm U) :
    (sourceTestFirst hm U u).1 = (u.1.1, 0) := rfl

@[simp] theorem sourceTestSecond_val (u : SourceTestSpace hm U) :
    (sourceTestSecond hm U u).1 = (0, u.1.2) := rfl

theorem sourceTestFirst_add_second (u : SourceTestSpace hm U) :
    sourceTestFirst hm U u + sourceTestSecond hm U u = u := by
  apply Subtype.ext
  change (u.1.1, 0) + (0, u.1.2) = u.1
  simp

/-- The exact covariance has no mixed real term between the two source components. -/
theorem sourceTestComponents_norm_sq (u : SourceTestSpace hm U) :
    ‖u‖ ^ 2 = ‖sourceTestFirst hm U u‖ ^ 2 + ‖sourceTestSecond hm U u‖ ^ 2 := by
  rw [sourceTestSpace_norm_sq, sourceTestSpace_norm_sq, sourceTestSpace_norm_sq]
  simp [timeZeroFourierCovariance, timeZeroFourierDiagonal, add_mul, Complex.add_re]

theorem norm_sourceTestFirst_le (u : SourceTestSpace hm U) :
    ‖sourceTestFirst hm U u‖ ≤ ‖u‖ := by
  have h := sourceTestComponents_norm_sq hm U u
  nlinarith [sq_nonneg ‖sourceTestSecond hm U u‖, norm_nonneg u,
    norm_nonneg (sourceTestFirst hm U u)]

theorem norm_sourceTestSecond_le (u : SourceTestSpace hm U) :
    ‖sourceTestSecond hm U u‖ ≤ ‖u‖ := by
  have h := sourceTestComponents_norm_sq hm U u
  nlinarith [sq_nonneg ‖sourceTestFirst hm U u‖, norm_nonneg u,
    norm_nonneg (sourceTestSecond hm U u)]

/-- Source test first continuous linear map of type `SourceTestSpace hm U →L[ℝ] SourceTestSpace hm
U`. -/
noncomputable def sourceTestFirstCLM : SourceTestSpace hm U →L[ℝ] SourceTestSpace hm U :=
  (sourceTestFirst hm U).mkContinuous 1 fun u => by
    simpa using norm_sourceTestFirst_le hm U u

/-- Source test second continuous linear map of type `SourceTestSpace hm U →L[ℝ] SourceTestSpace hm
U`. -/
noncomputable def sourceTestSecondCLM : SourceTestSpace hm U →L[ℝ] SourceTestSpace hm U :=
  (sourceTestSecond hm U).mkContinuous 1 fun u => by
    simpa using norm_sourceTestSecond_le hm U u

/-- The first component of the actual covariance completion. -/
noncomputable def sourceFirst : SourceHilbert hm U →L[ℝ] SourceHilbert hm U :=
  (sourceTestFirstCLM hm U).completion

/-- The second component of the actual covariance completion. -/
noncomputable def sourceSecond : SourceHilbert hm U →L[ℝ] SourceHilbert hm U :=
  (sourceTestSecondCLM hm U).completion

@[simp] theorem sourceFirst_coe (u : SourceTestSpace hm U) :
    sourceFirst hm U (u : SourceHilbert hm U) =
      (sourceTestFirst hm U u : SourceHilbert hm U) :=
  (sourceTestFirstCLM hm U).completion_apply_coe u

@[simp] theorem sourceSecond_coe (u : SourceTestSpace hm U) :
    sourceSecond hm U (u : SourceHilbert hm U) =
      (sourceTestSecond hm U u : SourceHilbert hm U) :=
  (sourceTestSecondCLM hm U).completion_apply_coe u

theorem sourceFirst_add_second (u : SourceHilbert hm U) :
    sourceFirst hm U u + sourceSecond hm U u = u := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq ((sourceFirst hm U).continuous.add (sourceSecond hm U).continuous)
      continuous_id) ?_
  intro v
  rw [sourceFirst_coe, sourceSecond_coe, ← UniformSpace.Completion.coe_add,
    sourceTestFirst_add_second]

/-- Pythagoras survives completion because both component maps are continuous. -/
theorem sourceComponents_norm_sq (u : SourceHilbert hm U) :
    ‖u‖ ^ 2 = ‖sourceFirst hm U u‖ ^ 2 + ‖sourceSecond hm U u‖ ^ 2 := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (continuous_norm.pow 2)
      (((sourceFirst hm U).continuous.norm.pow 2).add
        ((sourceSecond hm U).continuous.norm.pow 2))) ?_
  intro v
  simpa only [sourceFirst_coe, sourceSecond_coe, UniformSpace.Completion.norm_coe] using
    sourceTestComponents_norm_sq hm U v

theorem norm_sourceFirst_apply_le (u : SourceHilbert hm U) :
    ‖sourceFirst hm U u‖ ≤ ‖u‖ := by
  have h := sourceComponents_norm_sq hm U u
  nlinarith [sq_nonneg ‖sourceSecond hm U u‖, norm_nonneg u,
    norm_nonneg (sourceFirst hm U u)]

theorem norm_sourceSecond_apply_le (u : SourceHilbert hm U) :
    ‖sourceSecond hm U u‖ ≤ ‖u‖ := by
  have h := sourceComponents_norm_sq hm U u
  nlinarith [sq_nonneg ‖sourceFirst hm U u‖, norm_nonneg u,
    norm_nonneg (sourceSecond hm U u)]

theorem norm_sourceFirst_le_one : ‖sourceFirst hm U‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_sourceFirst_apply_le hm U u

theorem norm_sourceSecond_le_one : ‖sourceSecond hm U‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_sourceSecond_apply_le hm U u

theorem sourceFirst_idempotent (u : SourceHilbert hm U) :
    sourceFirst hm U (sourceFirst hm U u) = sourceFirst hm U u := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq ((sourceFirst hm U).continuous.comp (sourceFirst hm U).continuous)
      (sourceFirst hm U).continuous) ?_
  intro v
  simp only [sourceFirst_coe]
  rfl

theorem sourceSecond_idempotent (u : SourceHilbert hm U) :
    sourceSecond hm U (sourceSecond hm U u) = sourceSecond hm U u := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq ((sourceSecond hm U).continuous.comp (sourceSecond hm U).continuous)
      (sourceSecond hm U).continuous) ?_
  intro v
  simp only [sourceSecond_coe]
  rfl

theorem sourceFirst_second_eq_zero (u : SourceHilbert hm U) :
    sourceFirst hm U (sourceSecond hm U u) = 0 := by
  have h := sourceFirst_add_second hm U (sourceSecond hm U u)
  rw [sourceSecond_idempotent] at h
  exact add_right_cancel (h.trans (zero_add _).symm)

theorem sourceSecond_first_eq_zero (u : SourceHilbert hm U) :
    sourceSecond hm U (sourceFirst hm U u) = 0 := by
  have h := sourceFirst_add_second hm U (sourceFirst hm U u)
  rw [sourceFirst_idempotent] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

/-- The completed first component agrees with the literal `f` vector on tests. -/
theorem sourceEmbedding_first_coe (u : SourceTestSpace hm U) :
    sourceEmbedding hm U (sourceFirst hm U (u : SourceHilbert hm U)) =
      timeZeroL2 hm (u.1.1, 0) := by
  rw [sourceFirst_coe, sourceEmbedding_coe]
  rfl

/-- The completed second component agrees with the literal `iωg` vector on tests. -/
theorem sourceEmbedding_second_coe (u : SourceTestSpace hm U) :
    sourceEmbedding hm U (sourceSecond hm U (u : SourceHilbert hm U)) =
      timeZeroL2 hm (0, u.1.2) := by
  rw [sourceSecond_coe, sourceEmbedding_coe]
  rfl

end VacuumBellSeparation
