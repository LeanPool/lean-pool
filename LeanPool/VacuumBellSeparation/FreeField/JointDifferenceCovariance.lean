/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointDifferenceComponentPairing
public import LeanPool.VacuumBellSeparation.FreeField.FiniteProductSourceCompression

/-!
# Original product-minus-joint covariance in the total source norm

The zero-order kernel operator has zero same-ball pairings and the
negative original Fourier covariance on opposite balls. Bilinearity then
identifies its form on arbitrary sums of the two original regional tests.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian MeasureTheory Set Metric
open scoped InnerProductSpace

theorem jointComponent_test_separation {s : ℝ} (hs : 600 ≤ s)
    (a b : Fin 2) (hab : a ≠ b) (x y : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ closedBall (jointCenterIndex s a) 1)
    (hy : y ∈ closedBall (jointCenterIndex s b) 1) : 1 ≤ ‖x - y‖ := by
  have hc := jointCenterIndex_separated hs
  have hc' : 5 ≤ dist (jointCenterIndex s a) (jointCenterIndex s b) := by
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact hc
    · rw [dist_comm]
      exact hc
    · exact absurd rfl hab
  have hx' : dist (jointCenterIndex s a) x ≤ 1 := by
    simpa only [mem_closedBall, dist_comm] using hx
  have hy' : dist y (jointCenterIndex s b) ≤ 1 := hy
  have h₁ := dist_triangle (jointCenterIndex s a) x (jointCenterIndex s b)
  have h₂ := dist_triangle x y (jointCenterIndex s b)
  rw [dist_eq_norm x y] at h₂
  linarith

theorem jointDifferenceKernelOperator_pairing_component {μ s : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s) (a b : Fin 2)
    (u v : SourceTestSpace hμ (jointSourceRegion s))
    (hu : u.1 ∈ localizedTimeZeroSources (ball (jointCenterIndex s a) 1))
    (hv : v.1 ∈ localizedTimeZeroSources (ball (jointCenterIndex s b) 1)) :
    inner ℝ (u : SourceHilbert hμ (jointSourceRegion s))
      (jointDifferenceKernelOperator hμ hs (v : SourceHilbert hμ (jointSourceRegion s))) =
        if a = b then 0 else -timeZeroFourierCovariance μ u.1 v.1 := by
  have huf : Function.support u.1.1.1 ⊆ closedBall (jointCenterIndex s a) 1 :=
    ((subset_tsupport _).trans hu.1).trans ball_subset_closedBall
  have hug : Function.support u.1.2.1 ⊆ closedBall (jointCenterIndex s a) 1 :=
    ((subset_tsupport _).trans hu.2).trans ball_subset_closedBall
  have hvf : Function.support v.1.1.1 ⊆ closedBall (jointCenterIndex s b) 1 :=
    ((subset_tsupport _).trans hv.1).trans ball_subset_closedBall
  have hvg : Function.support v.1.2.1 ⊆ closedBall (jointCenterIndex s b) 1 :=
    ((subset_tsupport _).trans hv.2).trans ball_subset_closedBall
  unfold jointDifferenceKernelOperator jointErrorOperator
  rw [add_apply, inner_add_right,
    jointFieldDifference_pairing_component hμ hs a b u v huf hvf,
    jointMomentumDifference_pairing_component hμ hs a b u v hug hvg]
  by_cases hab : a = b
  · simp only [ite_eq_left hab, add_zero]
  · simp only [ite_eq_right hab]
    have hff (x y : EuclideanSpace ℝ (Fin 3)) (hx : u.1.1.1 x ≠ 0) (hy : v.1.1.1 y ≠ 0) :
        (1 : ℝ) ≤ ‖x - y‖ := jointComponent_test_separation hs a b hab x y (huf hx) (hvf hy)
    have hgg (x y : EuclideanSpace ℝ (Fin 3)) (hx : u.1.2.1 x ≠ 0) (hy : v.1.2.1 y ≠ 0) :
        (1 : ℝ) ≤ ‖x - y‖ := jointComponent_test_separation hs a b hab x y (hug hx) (hvg hy)
    have hfi : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        spatialFieldBesselKernel μ (p.1 - p.2) * u.1.1.1 p.1 * v.1.1.1 p.2) := by
      have h := (integrable_spatialFieldKernel_pairing hμ (by norm_num : (0 : ℝ) < 1)
        u.1.1 v.1.1 hff).re
      simp only [RCLike.re_eq_complex_re, ← Complex.ofReal_mul, Complex.ofReal_re] at h
      exact h
    have hgi : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        spatialMomentumBesselKernel μ (p.1 - p.2) * u.1.2.1 p.1 * v.1.2.1 p.2) := by
      have h := (integrable_spatialMomentumKernel_pairing hμ (by norm_num : (0 : ℝ) < 1)
        u.1.2 v.1.2 hgg).re
      simp only [RCLike.re_eq_complex_re, ← Complex.ofReal_mul, Complex.ofReal_re] at h
      exact h
    rw [timeZeroFourierCovariance_eq_bessel_kernel hμ (by norm_num : (0 : ℝ) < 1)
      u.1 v.1 hff hgg, ← MeasureTheory.Measure.volume_eq_prod, integral_add hfi hgi]
    ring

/-- No inverse of regional synthesis is assumed: all four inputs are
literal regional test sources in the original total covariance norm. -/
theorem jointDifferenceKernelOperator_pairing_sum {μ s : ℝ}
    (hμ : 0 < μ) (hs : 600 ≤ s)
    (u v : Fin 2 → SourceTestSpace hμ (jointSourceRegion s))
    (hu : ∀ i, (u i).1 ∈ localizedTimeZeroSources (ball (jointCenterIndex s i) 1))
    (hv : ∀ i, (v i).1 ∈ localizedTimeZeroSources (ball (jointCenterIndex s i) 1)) :
    inner ℝ ((u 0 : SourceHilbert hμ (jointSourceRegion s)) + (u 1 : SourceHilbert hμ
      (jointSourceRegion s)))
      (jointDifferenceKernelOperator hμ hs
        ((v 0 : SourceHilbert hμ (jointSourceRegion s)) + (v 1 : SourceHilbert hμ
          (jointSourceRegion s)))) =
      (inner ℝ (u 0 : SourceHilbert hμ (jointSourceRegion s)) (v 0 : SourceHilbert hμ
        (jointSourceRegion s)) +
        inner ℝ (u 1 : SourceHilbert hμ (jointSourceRegion s)) (v 1 : SourceHilbert hμ
          (jointSourceRegion s))) -
      inner ℝ ((u 0 : SourceHilbert hμ (jointSourceRegion s)) + (u 1 : SourceHilbert hμ
        (jointSourceRegion s)))
        ((v 0 : SourceHilbert hμ (jointSourceRegion s)) + (v 1 : SourceHilbert hμ
          (jointSourceRegion s))) := by
  simp only [map_add, inner_add_left, inner_add_right,
    jointDifferenceKernelOperator_pairing_component hμ hs 0 0 (u 0) (v 0) (hu 0) (hv 0),
    jointDifferenceKernelOperator_pairing_component hμ hs 0 1 (u 0) (v 1) (hu 0) (hv 1),
    jointDifferenceKernelOperator_pairing_component hμ hs 1 0 (u 1) (v 0) (hu 1) (hv 0),
    jointDifferenceKernelOperator_pairing_component hμ hs 1 1 (u 1) (v 1) (hu 1) (hv 1),
    sourceHilbert_test_inner_covariance, show (0 : Fin 2) ≠ 1 by decide,
    show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  ring

end VacuumBellSeparation
