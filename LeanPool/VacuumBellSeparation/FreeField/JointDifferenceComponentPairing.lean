/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPhysicalKernelRestriction
public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelComponentForm

/-! # The limiting kernel operator has the original physical component pairings -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian MeasureTheory Set Metric
open scoped SchwartzMap InnerProductSpace

theorem jointIndex_bool_eq (i j : Fin 2) :
    (decide (i = 1) = decide (j = 1)) ↔ i = j := by
  fin_cases i <;> fin_cases j <;> decide

theorem jointPolynomialErrorPatch_zero_sum {s : ℝ} (hs : 600 ≤ s)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (a b : Fin 2) (x : JointKernelSpace)
    (hx : x.fst ∈ closedBall (jointCenterIndex s a) 1)
    (hy : x.snd ∈ closedBall (jointCenterIndex s b) 1) :
    (∑ i : Fin 2, ∑ j : Fin 2, jointPolynomialErrorPatch hs F hF 0 i j x) =
      jointComponentKernel F (decide (a = 1)) (decide (b = 1))
        (jointPhysicalMidpoint s (jointComplexCoordinates x)) := by
  have h := jointSmoothCutoff_four_sum_on_component (jointCenterIndex s)
    (jointCenterIndex_separated hs)
    (fun i j => jointRealPolynomialError F s 0 (decide (i = 1)) (decide (j = 1))) a b x hx hy
  beta_reduce at h
  -- Each patch is the cut-off real error kernel, by definition.
  have hz (i j : Fin 2) : jointPolynomialErrorPatch hs F hF 0 i j x =
      jointSmoothCutoff (jointCenterIndex s i) (jointCenterIndex s j) x *
        jointRealPolynomialError F s 0 (decide (i = 1)) (decide (j = 1)) x := rfl
  simp only [hz]
  rw [h]
  simp only [jointRealPolynomialError, Function.comp_apply, jointPhysicalPolynomialError,
    jointMidpointPolynomial_zero, map_zero, sub_zero]

theorem jointFieldErrorPatch_zero_sum {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
    (a b : Fin 2) (x : JointKernelSpace)
    (hx : x.fst ∈ closedBall (jointCenterIndex s a) 1)
    (hy : x.snd ∈ closedBall (jointCenterIndex s b) 1) :
    (∑ i : Fin 2, ∑ j : Fin 2, jointPolynomialErrorPatch hs (jointNormalizedFieldKernel μ s)
      (jointNormalizedFieldKernel_analyticAt hμ (by linarith)) 0 i j x) =
        if a = b then 0 else -(spatialFieldBesselKernel μ (x.fst - x.snd) : ℂ) := by
  rw [jointPolynomialErrorPatch_zero_sum hs _ _ a b x hx hy,
    jointComponentFieldKernel_physical (by linarith : s ≠ 0)]
  by_cases hab : a = b
  · subst hab
    simp
  · have hd : decide (a = 1) ≠ decide (b = 1) := fun h => hab ((jointIndex_bool_eq a b).mp h)
    rw [ite_eq_right hd, ite_eq_right hab, spatialFieldBesselKernel_sub_comm μ x.snd x.fst]

theorem jointMomentumErrorPatch_zero_sum {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
    (a b : Fin 2) (x : JointKernelSpace)
    (hx : x.fst ∈ closedBall (jointCenterIndex s a) 1)
    (hy : x.snd ∈ closedBall (jointCenterIndex s b) 1) :
    (∑ i : Fin 2, ∑ j : Fin 2, jointPolynomialErrorPatch hs (jointNormalizedMomentumKernel μ s)
      (jointNormalizedMomentumKernel_analyticAt hμ (by linarith)) 0 i j x) =
        if a = b then 0 else -(spatialMomentumBesselKernel μ (x.fst - x.snd) : ℂ) := by
  rw [jointPolynomialErrorPatch_zero_sum hs _ _ a b x hx hy,
    jointComponentMomentumKernel_physical (by linarith : s ≠ 0)]
  by_cases hab : a = b
  · subst hab
    simp
  · have hd : decide (a = 1) ≠ decide (b = 1) := fun h => hab ((jointIndex_bool_eq a b).mp h)
    rw [ite_eq_right hd, ite_eq_right hab, spatialMomentumBesselKernel_sub_comm μ x.snd x.fst]

theorem joint_negative_real_kernel_integral
    (K : EuclideanSpace ℝ (Fin 3) → ℝ) (f g : SpatialTestFunction) :
    (∫ x : JointKernelSpace, (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * (-(K (x.fst - x.snd) : ℂ))).re =
      -(∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        K (p.1 - p.2) * f.1 p.1 * g.1 p.2) := by
  have he (x : JointKernelSpace) :
      (f.1 x.fst : ℂ) * (g.1 x.snd : ℂ) * (-(K (x.fst - x.snd) : ℂ)) =
        ((-(K (x.fst - x.snd) * f.1 x.fst * g.1 x.snd) : ℝ) : ℂ) := by
    push_cast
    ring
  simp_rw [he]
  rw [integral_complex_ofReal, Complex.ofReal_re, integral_neg]
  congr 1
  exact integral_jointKernel_ofLp (fun p => K (p.1 - p.2) * f.1 p.1 * g.1 p.2)

theorem jointFieldDifference_pairing_component {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
    (a b : Fin 2) (u v : SourceTestSpace hμ (jointSourceRegion s))
    (hu : Function.support u.1.1.1 ⊆ closedBall (jointCenterIndex s a) 1)
    (hv : Function.support v.1.1.1 ⊆ closedBall (jointCenterIndex s b) 1) :
    inner ℝ (u : SourceHilbert hμ (jointSourceRegion s))
      (jointFieldErrorOperator hμ hs 0 (v : SourceHilbert hμ (jointSourceRegion s))) =
      if a = b then 0 else -(∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        spatialFieldBesselKernel μ (p.1 - p.2) * u.1.1.1 p.1 * v.1.1.1 p.2) := by
  have h := jointFourFieldKernelOperator_pairing_component hμ (jointSourceRegion s)
    (jointCenterIndex s a) (jointCenterIndex s b) _ _
      (jointFieldErrorPatch_zero_sum hμ hs a b) u v hu hv
  change inner ℝ (u : SourceHilbert hμ (jointSourceRegion s))
    (jointFieldErrorOperator hμ hs 0 (v : SourceHilbert hμ (jointSourceRegion s))) = _ at h
  rw [h]
  by_cases hab : a = b
  · simp only [ite_eq_left hab, mul_zero, integral_zero, Complex.zero_re]
  · simp only [ite_eq_right hab]
    exact joint_negative_real_kernel_integral _ u.1.1 v.1.1

theorem jointMomentumDifference_pairing_component {μ s : ℝ} (hμ : 0 < μ) (hs : 600 ≤ s)
    (a b : Fin 2) (u v : SourceTestSpace hμ (jointSourceRegion s))
    (hu : Function.support u.1.2.1 ⊆ closedBall (jointCenterIndex s a) 1)
    (hv : Function.support v.1.2.1 ⊆ closedBall (jointCenterIndex s b) 1) :
    inner ℝ (u : SourceHilbert hμ (jointSourceRegion s))
      (jointMomentumErrorOperator hμ hs 0 (v : SourceHilbert hμ (jointSourceRegion s))) =
      if a = b then 0 else -(∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        spatialMomentumBesselKernel μ (p.1 - p.2) * u.1.2.1 p.1 * v.1.2.1 p.2) := by
  have h := jointFourMomentumKernelOperator_pairing_component hμ
    (jointCenterIndex s 0) (jointCenterIndex s 1) (jointCenterIndex s a) (jointCenterIndex s b)
    _ _ (jointMomentumErrorPatch_zero_sum hμ hs a b) u v hu hv
  change inner ℝ (u : SourceHilbert hμ (jointSourceRegion s))
    (jointMomentumErrorOperator hμ hs 0 (v : SourceHilbert hμ (jointSourceRegion s))) = _ at h
  rw [h]
  by_cases hab : a = b
  · simp only [ite_eq_left hab, mul_zero, integral_zero, Complex.zero_re]
  · simp only [ite_eq_right hab]
    exact joint_negative_real_kernel_integral _ u.1.2 v.1.2

end VacuumBellSeparation
