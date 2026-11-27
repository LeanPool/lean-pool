/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Actual bounded forms on the real Hilbert completion

A bounded real bilinear form extends in both variables by the actual
completion maps. Riesz representation then gives a bounded operator on
that completion with the same norm bound and the original test pairings.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Gaussian

open UniformSpace
open scoped InnerProductSpace

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_fromCompletion_le (L : E →L[ℝ] F) : ‖L.fromCompletion‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro x
  refine Completion.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro y
  simpa only [ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe] using
    L.le_opNorm y

/-- Extension in the dual variable is itself an actual contraction. -/
def completionDualLift (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E →L[ℝ] ℝ) →L[ℝ] (Completion E →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun L => L.fromCompletion
      map_add' := by
        intro L M
        apply ContinuousLinearMap.fromCompletion_unique
        intro x
        simp only [add_apply, ContinuousLinearMap.fromCompletion_apply_coe]
      map_smul' := by
        intro c L
        apply ContinuousLinearMap.fromCompletion_unique
        intro x
        simp only [smul_apply, ContinuousLinearMap.fromCompletion_apply_coe,
          RingHom.id_apply] }
    1 (fun L => by
      change ‖L.fromCompletion‖ ≤ 1 * ‖L‖
      simpa only [one_mul] using norm_fromCompletion_le L)

@[simp] theorem completionDualLift_apply (L : E →L[ℝ] ℝ) :
    completionDualLift E L = L.fromCompletion := rfl

theorem norm_completionDualLift_le : ‖completionDualLift E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  simpa only [completionDualLift_apply, one_mul] using norm_fromCompletion_le L

/-- Both variables are extended; no completion-boundedness premise is added. -/
def completedRealBilinear (B : E →L[ℝ] E →L[ℝ] ℝ) :
    Completion E →L[ℝ] Completion E →L[ℝ] ℝ :=
  (completionDualLift E).comp B.fromCompletion

@[simp] theorem completedRealBilinear_coe (B : E →L[ℝ] E →L[ℝ] ℝ) (x y : E) :
    completedRealBilinear B (x : Completion E) (y : Completion E) = B x y := by
  simp only [completedRealBilinear, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.fromCompletion_apply_coe, completionDualLift_apply]

theorem norm_completedRealBilinear_le (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖completedRealBilinear B‖ ≤ ‖B‖ := by
  calc
    _ ≤ ‖completionDualLift E‖ * ‖B.fromCompletion‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖B‖ := mul_le_mul norm_completionDualLift_le (norm_fromCompletion_le B)
      (norm_nonneg B.fromCompletion) zero_le_one
    _ = _ := one_mul _

end General

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual Riesz operator of the completed original bilinear form. -/
def completedRealFormOperator (B : E →L[ℝ] E →L[ℝ] ℝ) :
    Completion E →L[ℝ] Completion E :=
  let riesz := (InnerProductSpace.toDual ℝ (Completion E)).symm.toContinuousLinearEquiv
  riesz.toContinuousLinearMap.comp (completedRealBilinear B).flip

theorem inner_completedRealFormOperator (B : E →L[ℝ] E →L[ℝ] ℝ)
    (x y : Completion E) :
    inner ℝ x (completedRealFormOperator B y) = completedRealBilinear B x y := by
  change inner ℝ x ((InnerProductSpace.toDual ℝ (Completion E)).symm
    ((completedRealBilinear B).flip y)) = completedRealBilinear B x y
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

@[simp] theorem inner_completedRealFormOperator_coe (B : E →L[ℝ] E →L[ℝ] ℝ)
    (x y : E) :
    inner ℝ (x : Completion E) (completedRealFormOperator B (y : Completion E)) = B x y := by
  rw [inner_completedRealFormOperator, completedRealBilinear_coe]

theorem norm_completedRealFormOperator_le (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖completedRealFormOperator B‖ ≤ ‖B‖ := by
  have hpoint (x y : Completion E) :
      ‖completedRealBilinear B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by
    refine Completion.induction_on₂ x y (isClosed_le (by fun_prop) (by fun_prop)) ?_
    intro a b
    simpa only [completedRealBilinear_coe, Completion.norm_coe] using B.le_opNorm₂ a b
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro y
  change ‖(InnerProductSpace.toDual ℝ (Completion E)).symm
    ((completedRealBilinear B).flip y)‖ ≤ ‖B‖ * ‖y‖
  rw [(InnerProductSpace.toDual ℝ (Completion E)).symm.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg B) (norm_nonneg y))
  intro x
  change ‖completedRealBilinear B x y‖ ≤ (‖B‖ * ‖y‖) * ‖x‖
  simpa only [mul_right_comm] using hpoint x y

end Hilbert
end VacuumBellSeparation.Gaussian
