/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPhysicalCoordinates
public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelPlancherel
public import LeanPool.VacuumBellSeparation.FreeField.SpatialKernelTaylorReal

/-!
# The actual Euclidean pair included in the six complex coordinates

The domain is the original Euclidean product carrying six-dimensional
Lebesgue measure. Its coordinate inclusion has operator norm at most one.
The component centres are the literal original spatial centres.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Metric

/-- Real-linear inclusion of the two actual spatial triples in complex coordinates. -/
def jointComplexCoordinates : JointKernelSpace →L[ℝ] (Fin 6 → ℂ) :=
  ContinuousLinearMap.pi (fun j => Fin.addCases
    (fun i : Fin 3 => Complex.ofRealCLM.comp
      ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).comp
        (WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))))
    (fun i : Fin 3 => Complex.ofRealCLM.comp
      ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).comp
        (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))))) j)

@[simp] theorem jointComplexCoordinates_left (x : JointKernelSpace) (i : Fin 3) :
    jointComplexCoordinates x (Fin.castAdd 3 i) = (x.fst i : ℂ) := by
  simp [jointComplexCoordinates]

theorem jointComplexCoordinates_right (x : JointKernelSpace) (i : Fin 3) :
    jointComplexCoordinates x (Fin.natAdd 3 i) = (x.snd i : ℂ) := by
  simp only [jointComplexCoordinates, ContinuousLinearMap.pi_apply, Fin.addCases_right]
  rfl

theorem norm_jointComplexCoordinates_le : ‖jointComplexCoordinates‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound jointComplexCoordinates (by norm_num)
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  refine Fin.addCases (m := 3) (n := 3) (fun i => ?_) (fun i => ?_) j
  · rw [jointComplexCoordinates_left, Complex.norm_real]
    exact (PiLp.norm_apply_le x.fst i).trans
      (WithLp.norm_fst_le (EuclideanSpace ℝ (Fin 3)) x)
  · rw [jointComplexCoordinates_right, Complex.norm_real]
    exact (PiLp.norm_apply_le x.snd i).trans
      (WithLp.norm_snd_le (EuclideanSpace ℝ (Fin 3)) x)

/-- Joint spatial center defined as `if a then spatialAxisDisplacement s 0 else 0`. -/
def jointSpatialCenter (s : ℝ) (a : Bool) : EuclideanSpace ℝ (Fin 3) :=
  if a then spatialAxisDisplacement s 0 else 0

theorem jointPhysicalComponentCenter_left (s : ℝ) (a b : Bool) (i : Fin 3) :
    jointPhysicalComponentCenter a b s (Fin.castAdd 3 i) = (jointSpatialCenter s a i : ℂ) := by
  rw [jointPhysicalComponentCenter_eq]
  fin_cases i <;> cases a <;>
    simp [jointSpatialCenter, spatialAxisDisplacement]

theorem jointPhysicalComponentCenter_right (s : ℝ) (a b : Bool) (i : Fin 3) :
    jointPhysicalComponentCenter a b s (Fin.natAdd 3 i) = (jointSpatialCenter s b i : ℂ) := by
  rw [jointPhysicalComponentCenter_eq]
  fin_cases i <;> cases b <;>
    simp [jointSpatialCenter, spatialAxisDisplacement]

theorem jointComplexCoordinates_in_component (s r : ℝ) (a b : Bool) (x : JointKernelSpace)
    (hx : x.fst ∈ closedBall (jointSpatialCenter s a) r)
    (hy : x.snd ∈ closedBall (jointSpatialCenter s b) r) :
    InPhysicalJointComponent a b s r (jointComplexCoordinates x) := by
  have hx' : ‖x.fst - jointSpatialCenter s a‖ ≤ r := by
    simpa only [mem_closedBall, dist_eq_norm] using hx
  have hy' : ‖x.snd - jointSpatialCenter s b‖ ≤ r := by
    simpa only [mem_closedBall, dist_eq_norm] using hy
  intro j
  refine Fin.addCases (m := 3) (n := 3) (fun i => ?_) (fun i => ?_) j
  · rw [jointComplexCoordinates_left, jointPhysicalComponentCenter_left,
      ← Complex.ofReal_sub, Complex.norm_real]
    exact (PiLp.norm_apply_le (x.fst - jointSpatialCenter s a) i).trans hx'
  · rw [jointComplexCoordinates_right, jointPhysicalComponentCenter_right,
      ← Complex.ofReal_sub, Complex.norm_real]
    exact (PiLp.norm_apply_le (x.snd - jointSpatialCenter s b) i).trans hy'

end VacuumBellSeparation
