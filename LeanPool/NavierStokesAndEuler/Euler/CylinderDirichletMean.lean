/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletNaturality
import LeanPool.NavierStokesAndEuler.Euler.CylinderTranslationAdjoint
import LeanPool.NavierStokesAndEuler.Euler.LpOperatorFieldAlgebra

/-!
# Actual zero angular mean of the history solution

Angle-independent coefficients commute with the genuine cylinder average,
including the adjoint test maps. The constructed inverse and its continuous
velocity therefore preserve zero mean. No pointwise mean condition is assumed
on the solution.
-/

@[expose] public section


noncomputable section

namespace EulerLpCylinderRectangular

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerCylinderAngleAverage
  EulerBoundedFieldCalculus
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem fullOperatorMap_adjoint (Q : Space →ᵇ U →L[ℝ] E) :
    (fullOperatorMap (E := U) (F := E) P Q).adjoint =
      fullOperatorMap (E := E) (F := U) P (adjointMap (α := Space) (U := U) (E := E) Q) := by
  rw [fullOperatorMap_apply, EulerLpOperatorField.full_adjoint]
  rfl

theorem average_fullOperator_back (Q : Space →ᵇ U →L[ℝ] E) (u : CylinderL2 P U) :
    fullOperatorMap (E := U) (F := E) P Q ((average (V := U) P).adjoint u) =
      (average (V := E) P).adjoint (fullOperatorMap (E := U) (F := E) P Q u) := by
  apply ext_inner_right ℝ
  intro v
  have hc := average_fullOperator P (adjointMap (α := Space) (U := U) (E := E) Q) v
  rw [← fullOperatorMap_adjoint] at hc
  rw [adjoint_inner_left, ← adjoint_inner_right, adjoint_inner_left, hc, adjoint_inner_right]

end EulerLpCylinderRectangular

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerCylinderAngleAverage EulerTimeLp EulerTimeLpBoundedMap
  EulerTransverseGramInverse

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

theorem velocityPath_average (f : TimeLp T (CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.velocityPath P (timeLift T (average (V := E) P) f) t =
      average (V := U) P (D.velocityPath P f t) :=
  D.velocityPath_intertwines P D (average P) (average P)
    (fun t u => (average_fullOperator P (D.Q t) u).symm)
    (fun t u => (average_fullOperator P (D.Q₁ t) u).symm)
    (fun t u => average_fullOperator_back P (D.Q t) u)
    (fun t u => average_fullOperator_back P (D.Q₁ t) u)
    (fun t u => (average_fullOperator P (D.H t) u).symm) f t

theorem accelerationPath_average (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.accelerationPath P (pathAverage P f) t = average P (D.accelerationPath P f t) :=
  D.accelerationPath_intertwines P D (average P) (average P)
    (fun t u => (average_fullOperator P (D.Q t) u).symm)
    (fun t u => (average_fullOperator P (D.Q₁ t) u).symm)
    (fun t u => average_fullOperator_back P (D.Q t) u)
    (fun t u => average_fullOperator_back P (D.Q₁ t) u)
    (fun t u => (average_fullOperator P (D.H t) u).symm) f t

theorem physicalVelocity_average (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.physicalVelocity P (pathAverage P f) t = average P (D.physicalVelocity P f t) :=
  D.physicalVelocity_intertwines P D (average P) (average P)
    (fun t u => (average_fullOperator P (D.Q t) u).symm)
    (fun t u => (average_fullOperator P (D.Q₁ t) u).symm)
    (fun t u => average_fullOperator_back P (D.Q t) u)
    (fun t u => average_fullOperator_back P (D.Q₁ t) u)
    (fun t u => (average_fullOperator P (D.H t) u).symm) f t

theorem physicalDerivative_average (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.physicalDerivative P (pathAverage P f) t = average P (D.physicalDerivative P f t) :=
  D.physicalDerivative_intertwines P D (average P) (average P)
    (fun t u => (average_fullOperator P (D.Q t) u).symm)
    (fun t u => (average_fullOperator P (D.Q₁ t) u).symm)
    (fun t u => average_fullOperator_back P (D.Q t) u)
    (fun t u => average_fullOperator_back P (D.Q₁ t) u)
    (fun t u => (average_fullOperator P (D.H t) u).symm) f t

theorem accelerationPath_zero (t : Icc (0 : ℝ) T) : D.accelerationPath P 0 t = 0 := by
  have hz : pathLp T D.time_pos.le (0 : C(Icc (0 : ℝ) T,CylinderL2 P E)) = 0 :=
    map_zero (pathLpOperator T D.time_pos.le)
  change gramInverse (D.frame P t) D.lower D.lower_pos (D.frame_lower P t)
    ((D.frame P t).adjoint (0-(2 : ℝ) • D.frameDerivative P t
      (D.velocityPath P (pathLp T D.time_pos.le 0) t))) = 0
  rw [hz]
  simp only [map_zero,ContinuousMap.zero_apply,smul_zero,sub_zero]

theorem physicalVelocity_zero (t : Icc (0 : ℝ) T) : D.physicalVelocity P 0 t = 0 := by
  have hz : pathLp T D.time_pos.le (0 : C(Icc (0 : ℝ) T,CylinderL2 P E)) = 0 :=
    map_zero (pathLpOperator T D.time_pos.le)
  change D.frame P t (D.velocityPath P (pathLp T D.time_pos.le 0) t) = 0
  rw [hz]
  simp only [map_zero,ContinuousMap.zero_apply]

theorem physicalDerivative_zero (t : Icc (0 : ℝ) T) : D.physicalDerivative P 0 t = 0 := by
  have hz : pathLp T D.time_pos.le (0 : C(Icc (0 : ℝ) T,CylinderL2 P E)) = 0 :=
    map_zero (pathLpOperator T D.time_pos.le)
  change D.frameDerivative P t (D.velocityPath P (pathLp T D.time_pos.le 0) t) +
    D.frame P t (D.accelerationPath P 0 t) = 0
  rw [hz,D.accelerationPath_zero P t]
  simp only [map_zero,ContinuousMap.zero_apply,add_zero]

variable (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (hf : ∀ t, average P (f t) = 0)

omit [CompleteSpace E] in
include hf in
private theorem averagedPath_zero : pathAverage P f = 0 := by
  apply ContinuousMap.ext
  intro t
  exact hf t

include hf in
theorem velocityPath_mean_zero (t : Icc (0 : ℝ) T) :
    average P (D.velocityPath P (pathLp T D.time_pos.le f) t) = 0 := by
  have hz : timeLift T (average (V := E) P) (pathLp T D.time_pos.le f) = 0 := by
    rw [← pathLp_timeLift]
    change pathLp T D.time_pos.le (pathAverage P f) = 0
    rw [averagedPath_zero P f hf]
    exact map_zero (pathLpOperator T D.time_pos.le)
  have h := D.velocityPath_average P (pathLp T D.time_pos.le f) t
  rw [hz,map_zero,ContinuousMap.zero_apply] at h
  exact h.symm

include hf in
theorem accelerationPath_mean_zero (t : Icc (0 : ℝ) T) :
    average P (D.accelerationPath P f t) = 0 := by
  rw [← D.accelerationPath_average P f t,averagedPath_zero P f hf,D.accelerationPath_zero P t]

include hf in
theorem physicalVelocity_mean_zero (t : Icc (0 : ℝ) T) :
    average P (D.physicalVelocity P f t) = 0 := by
  rw [← D.physicalVelocity_average P f t,averagedPath_zero P f hf,D.physicalVelocity_zero P t]

include hf in
theorem physicalDerivative_mean_zero (t : Icc (0 : ℝ) T) :
    average P (D.physicalDerivative P f t) = 0 := by
  rw [← D.physicalDerivative_average P f t,averagedPath_zero P f hf,D.physicalDerivative_zero P t]

end EulerCylinderDirichlet.Coefficients
