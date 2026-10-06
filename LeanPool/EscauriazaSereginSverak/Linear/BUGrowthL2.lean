/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# BUGrowth L2

Local square-integrability consequences of backward-uniqueness growth bounds.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A Gaussian growth bound makes the velocity square-integrable on bounded
subsets of the half-space cylinder (`thm:bu`). -/
theorem bu_growth_implies_local_l2
    (M : ℝ) (hM : 0 < M) (w : ParabolicPoint → Vec3)
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤ Real.exp (M * vec3EuclideanNorm z.1 ^ 2)) :
    ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  intro S hS hSbounded
  obtain ⟨R, hRpos, hR⟩ :=
    hSbounded.subset_ball_lt 0
      (show ParabolicPoint from ((0 : Vec3), (0 : ℝ)))
  let T := R + 1
  let Q := spaceTimeSet (vec3Ball 0 R) (Ioo (-T ^ 2) (T ^ 2))
  have hSsubQ : S ⊆ Q := by
    intro z hz
    have hzball : z ∈ Metric.ball
        (show ParabolicPoint from ((0 : Vec3), (0 : ℝ))) R := hR hz
    have hdist : parabolicDist z ((0 : Vec3), (0 : ℝ)) < R := by
      have hdist' := Metric.mem_ball.mp hzball
      rw [dist_eq_parabolicDist] at hdist'
      exact hdist'
    have hmax : max (vec3EuclideanNorm z.1) (Real.sqrt |z.2|) < R := by
      simpa [parabolicDist] using hdist
    have hx : z.1 ∈ vec3Ball 0 R := by
      simpa only [mem_vec3Ball, sub_zero] using lt_of_le_of_lt (le_max_left _ _) hmax
    have hroot : Real.sqrt |z.2| < R := lt_of_le_of_lt (le_max_right _ _) hmax
    have htAbs : |z.2| < R ^ 2 := by
      have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg |z.2|) hRpos.le).2 hroot
      simpa only [Real.sq_sqrt (abs_nonneg _)] using hsq
    have ht : -R ^ 2 < z.2 ∧ z.2 < R ^ 2 := (abs_lt.mp htAbs)
    have hTgt : R ^ 2 < T ^ 2 := by
      dsimp [T]
      nlinarith only [hRpos]
    change z.1 ∈ vec3Ball 0 R ∧ z.2 ∈ Ioo (-T ^ 2) (T ^ 2)
    exact ⟨hx, ⟨lt_trans (neg_lt_neg hTgt) ht.1,
      lt_trans ht.2 hTgt⟩⟩
  have hQmeasure : volume Q < ⊤ := by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change ((volume : Measure Vec3).prod (volume : Measure ℝ))
      (vec3Ball 0 R ×ˢ Ioo (-T ^ 2) (T ^ 2)) < ⊤
    rw [Measure.prod_prod, Real.volume_Ioo]
    exact ENNReal.mul_lt_top
      (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top (x := 0))
      ENNReal.ofReal_lt_top
  let K : ℝ := Real.exp (M * R ^ 2)
  have hpoint (z : ParabolicPoint) (hz : z ∈ S) :
      ‖w z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal K ^ (2 : ℝ) := by
    have hzB : z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) := hS hz
    have hzball : z ∈ Metric.ball
        (show ParabolicPoint from ((0 : Vec3), (0 : ℝ))) R := hR hz
    have hdist : parabolicDist z ((0 : Vec3), (0 : ℝ)) < R := by
      have hdist' := Metric.mem_ball.mp hzball
      rw [dist_eq_parabolicDist] at hdist'
      exact hdist'
    have hmax : max (vec3EuclideanNorm z.1) (Real.sqrt |z.2|) < R := by
      simpa [parabolicDist] using hdist
    have hxEuclid : vec3EuclideanNorm z.1 ≤ R := (le_max_left _ _).trans hmax.le
    have hxSquare : vec3EuclideanNorm z.1 ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (vec3EuclideanNorm_nonneg _) hRpos.le).2 hxEuclid
    have hgrowth' := hgrowth z hzB
    have hwNorm : ‖w z‖ ≤ K := by
      calc
        ‖w z‖ ≤ vec3EuclideanNorm (w z) := norm_le_vec3EuclideanNorm _
        _ ≤ Real.exp (M * vec3EuclideanNorm z.1 ^ 2) := hgrowth'
        _ ≤ Real.exp (M * R ^ 2) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxSquare hM.le)
        _ = K := rfl
    have hwENN : ‖w z‖ₑ ≤ ENNReal.ofReal K := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hwNorm
    exact ENNReal.rpow_le_rpow hwENN (by norm_num)
  calc
    (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ)) ≤
        ∫⁻ _ in S, ENNReal.ofReal K ^ (2 : ℝ) :=
      setLIntegral_mono measurable_const hpoint
    _ = ENNReal.ofReal K ^ (2 : ℝ) * volume S := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal K ^ (2 : ℝ) * volume Q := by
      gcongr
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hQmeasure

end ESS
