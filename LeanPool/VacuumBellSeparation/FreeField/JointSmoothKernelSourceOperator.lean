/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelForms

/-!
# Actual smooth-kernel operators on the total-source completion

These operators are obtained from the literal compact-test integrals in
the original joint covariance norm. The constants retain their explicit
mass dependence; cutoff and derivative estimates are separate inputs to
later applications of the displayed sixteen-term kernel energy.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform InnerProductSpace

/-- Field form on the genuine source completion of an arbitrary region. -/
def jointFieldKernelOperator {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (K : SchwartzMap JointKernelSpace ℂ) :
    SourceHilbert hμ U →L[ℝ] SourceHilbert hμ U :=
  Gaussian.completedRealFormOperator
    (boundedJointKernelTestForm (sourceFieldTestProjection hμ U) K
      (show 0 ≤ 2 * max 1 μ by positivity) (jointTestWeight_first_le_source_norm hμ U))

theorem jointFieldKernelOperator_pairing {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (K : SchwartzMap JointKernelSpace ℂ)
    (u v : SourceTestSpace hμ U) :
    inner ℝ (u : SourceHilbert hμ U) (jointFieldKernelOperator hμ U K (v : SourceHilbert hμ U)) =
      (∫ x : JointKernelSpace, (u.1.1.1 x.fst : ℂ) * (v.1.1.1 x.snd : ℂ) * K x).re := by
  unfold jointFieldKernelOperator
  rw [Gaussian.inner_completedRealFormOperator_coe]
  rfl

theorem norm_jointFieldKernelOperator_le {μ : ℝ} (hμ : 0 < μ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (K : SchwartzMap JointKernelSpace ℂ) :
    ‖jointFieldKernelOperator hμ U K‖ ≤
      (2 * max 1 μ) * Real.sqrt (jointKernelDerivativeEnergy K) := by
  apply (Gaussian.norm_completedRealFormOperator_le _).trans
  exact norm_boundedJointKernelTestForm_le (sourceFieldTestProjection hμ U) K _ _

/-- Momentum form on the genuine joint completion of the two-ball union. -/
def jointMomentumKernelOperator {μ : ℝ} (hμ : 0 < μ)
    (a b : EuclideanSpace ℝ (Fin 3)) (K : SchwartzMap JointKernelSpace ℂ) :
    SourceHilbert hμ (Metric.ball a 1 ∪ Metric.ball b 1) →L[ℝ]
      SourceHilbert hμ (Metric.ball a 1 ∪ Metric.ball b 1) :=
  Gaussian.completedRealFormOperator
    (boundedJointKernelTestForm
      (sourceMomentumTestProjection hμ (Metric.ball a 1 ∪ Metric.ball b 1)) K
      (by norm_num : (0 : ℝ) ≤ 4) (jointTestWeight_second_le_source_norm hμ a b))

theorem jointMomentumKernelOperator_pairing {μ : ℝ} (hμ : 0 < μ)
    (a b : EuclideanSpace ℝ (Fin 3)) (K : SchwartzMap JointKernelSpace ℂ)
    (u v : SourceTestSpace hμ (Metric.ball a 1 ∪ Metric.ball b 1)) :
    inner ℝ (u : SourceHilbert hμ (Metric.ball a 1 ∪ Metric.ball b 1))
      (jointMomentumKernelOperator hμ a b K
        (v : SourceHilbert hμ (Metric.ball a 1 ∪ Metric.ball b 1))) =
      (∫ x : JointKernelSpace, (u.1.2.1 x.fst : ℂ) * (v.1.2.1 x.snd : ℂ) * K x).re := by
  unfold jointMomentumKernelOperator
  rw [Gaussian.inner_completedRealFormOperator_coe]
  rfl

theorem norm_jointMomentumKernelOperator_le {μ : ℝ} (hμ : 0 < μ)
    (a b : EuclideanSpace ℝ (Fin 3)) (K : SchwartzMap JointKernelSpace ℂ) :
    ‖jointMomentumKernelOperator hμ a b K‖ ≤ 4 * Real.sqrt (jointKernelDerivativeEnergy K) := by
  apply (Gaussian.norm_completedRealFormOperator_le _).trans
  exact norm_boundedJointKernelTestForm_le
    (sourceMomentumTestProjection hμ (Metric.ball a 1 ∪ Metric.ball b 1)) K _ _

end VacuumBellSeparation
