/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.CoefficientPredual
public import LeanPool.VacuumBellSeparation.Bell.WeakCompactDualEvaluation
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
The original concrete VNA is isometrically the full continuous dual of its
norm-closed original-H coefficient space. Compactness is proved using its
actual WOT unit ball and evaluation of every coefficient-closure member.
There is no assumed onto map, faithful state, separability or normality
premise, and no substitute representation of the algebra.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Metric
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The previously proved norm equality bundles the literal evaluation map. -/
def coefficientPredualEvaluationLI (M : VonNeumannAlgebra H) :
    M.toStarSubalgebra →ₗᵢ[ℂ] StrongDual ℂ (coefficientPredual M) where
  toFun := coefficientPredualEvaluation M
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [coefficientPredualEvaluation_apply, map_add, add_apply]
  map_smul' c a := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [coefficientPredualEvaluation_apply, map_smul, smul_apply,
      RingHom.id_apply]
  norm_map' := coefficientPredualEvaluation_norm M

@[simp] theorem coefficientPredualEvaluationLI_apply (M : VonNeumannAlgebra H)
    (a : M.toStarSubalgebra) :
    coefficientPredualEvaluationLI M a = coefficientPredualEvaluation M a := rfl

/-- The genuine original operator unit ball has weak-star compact evaluation
image, with no assertion of operator-norm compactness. -/
theorem isCompact_coefficientPredualEvaluation_unitBall (M : VonNeumannAlgebra H) :
    IsCompact ((fun a : M.toStarSubalgebra =>
      StrongDual.toWeakDual (coefficientPredualEvaluation M a)) ''
      Metric.closedBall (0 : M.toStarSubalgebra) 1) := by
  let : CompactSpace (vnaWOTBall M 1) :=
    isCompact_iff_compactSpace.mp (isCompact_vna_unitBall_wot M)
  let b : vnaWOTBall M 1 → WeakDual ℂ (coefficientPredual M) := fun T =>
    StrongDual.toWeakDual (coefficientPredualEvaluation M (vnaWOTBallElement T))
  have hb : Continuous b := by
    apply WeakDual.continuous_of_continuous_eval
    intro f
    exact continuous_vnaWOTBall_eval_of_mem_coefficientPredual M 1 f.1 f.2
  have he : ((fun a : M.toStarSubalgebra =>
      StrongDual.toWeakDual (coefficientPredualEvaluation M a)) ''
      Metric.closedBall (0 : M.toStarSubalgebra) 1) = Set.range b := by
    ext F
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨ContinuousLinearMapWOT.ofCLM (a : H →L[ℂ] H), a.2,
        mem_closedBall_zero_iff.mp ha⟩, rfl⟩
    · rintro ⟨T, rfl⟩
      exact ⟨vnaWOTBallElement T, mem_closedBall_zero_iff.mpr T.2.2, rfl⟩
  rw [he]
  exact isCompact_range hb

/-- Every functional of norm at most one is literally evaluation at an
operator of norm at most one in the original VNA. -/
theorem exists_coefficientPredualEvaluation_unitBall (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) (hF : ‖F‖ ≤ 1) :
    ∃ a : M.toStarSubalgebra, ‖a‖ ≤ 1 ∧ coefficientPredualEvaluation M a = F := by
  exact exists_unitBall_preimage_of_isCompact_evaluation (coefficientPredual M)
    (coefficientPredualEvaluationLI M).toLinearMap
    (coefficientPredualEvaluation_apply M)
    (isCompact_coefficientPredualEvaluation_unitBall M) F hF

theorem coefficientPredualEvaluation_surjective (M : VonNeumannAlgebra H) :
    Function.Surjective (coefficientPredualEvaluation M) := by
  exact surjective_of_isCompact_evaluation (coefficientPredual M)
    (coefficientPredualEvaluationLI M).toLinearMap
    (coefficientPredualEvaluation_apply M)
    (isCompact_coefficientPredualEvaluation_unitBall M)

/-- The concrete coefficient closure is an actual isometric predual of the
original VNA. The forward map remains the literal evaluation pairing. -/
def coefficientPredualDualEquiv (M : VonNeumannAlgebra H) :
    M.toStarSubalgebra ≃ₗᵢ[ℂ] StrongDual ℂ (coefficientPredual M) :=
  LinearIsometryEquiv.ofSurjective (coefficientPredualEvaluationLI M)
    (coefficientPredualEvaluation_surjective M)

@[simp] theorem coefficientPredualDualEquiv_apply (M : VonNeumannAlgebra H)
    (a : M.toStarSubalgebra) (f : coefficientPredual M) :
    coefficientPredualDualEquiv M a f = f.1 a := rfl

end VacuumBellSeparation.Bipartite
