/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsDefinition
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# A concrete good point

This file supplies a satisfiability witness for `IsGoodPoint`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The zero fields provide a concrete inhabitant of the good-point interface. -/
theorem isGoodPoint_zero (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    IsGoodPoint ε₀ (fun _ => 0) (fun _ => 0)
      ((0 : Vec3), -(1 / 2 : ℝ)) := by
  let zc : ParabolicPoint := ((0 : Vec3), -(1 / 2 : ℝ))
  change IsGoodPoint ε₀ (fun _ => 0) (fun _ => 0) zc
  refine ⟨?_, 1 / 4, by norm_num, ?_, ?_, ?_⟩
  · change (0 : Vec3) ∈ vec3Ball 0 1 ∧ (-(1 / 2 : ℝ)) ∈ Ioc (-1) 0
    constructor
    · simp [vec3Ball, vec3EuclideanNorm_zero]
    · norm_num
  · intro z hz
    rcases hz with ⟨hx, ht⟩
    change vec3EuclideanNorm (z.1 - 0) < 1 ∧ z.2 ∈ Ioo (-1) 0
    constructor
    · have hnorm : vec3EuclideanNorm (z.1 - 0) < 1 / 4 := hx
      exact hnorm.trans (by norm_num)
    · rcases ht with ⟨hlt, hgt⟩
      constructor
      · have hlower : -(1 / 2 : ℝ) - (1 / 4 : ℝ) ^ 2 < z.2 := hlt
        linarith only [hlower]
      · change z.2 < -(1 / 2 : ℝ) at hgt
        exact lt_trans hgt (by norm_num)
  · have hbound : parabolicCylinder (0 : Vec3) (-(1 / 2 : ℝ)) (1 / 4 : ℝ) ⊆
        Metric.closedBall zc (1 / 4 : ℝ) ∩
          {z : ParabolicPoint | z.2 ≤ -(1 / 2 : ℝ)} := by
      intro z hz
      rcases hz with ⟨hx, ht, htop⟩
      refine ⟨?_, htop⟩
      change dist z zc ≤ 1 / 4
      rw [dist_eq_parabolicDist, parabolicDist]
      change max (vec3EuclideanNorm (z.1 - 0))
        (Real.sqrt |z.2 - (-(1 / 2 : ℝ))|) ≤ 1 / 4
      apply max_le
      · exact le_of_lt hx
      · have htime : |z.2 - (-(1 / 2 : ℝ))| ≤ (1 / 4 : ℝ) ^ 2 := by
          rw [abs_le]
          constructor
          · linarith only [ht]
          · linarith only [htop]
        have hsqrt : Real.sqrt |z.2 - (-(1 / 2 : ℝ))| ≤ 1 / 4 := by
          nlinarith only [htime,
            Real.sq_sqrt (abs_nonneg (z.2 - (-(1 / 2 : ℝ)))),
            Real.sqrt_nonneg |z.2 - (-(1 / 2 : ℝ))|]
        exact hsqrt
    have hclosed : IsClosed
        (Metric.closedBall zc (1 / 4 : ℝ) ∩
          {z : ParabolicPoint | z.2 ≤ -(1 / 2 : ℝ)}) := by
      exact Metric.isClosed_closedBall.inter
        (isClosed_Iic.preimage continuous_snd_parabolicPoint)
    have hclosure : closure (parabolicCylinder (0 : Vec3) (-(1 / 2 : ℝ)) (1 / 4 : ℝ)) ⊆
        Metric.closedBall zc (1 / 4 : ℝ) ∩
          {z : ParabolicPoint | z.2 ≤ -(1 / 2 : ℝ)} :=
      closure_minimal hbound hclosed
    intro z hz
    rcases hclosure hz with ⟨hzball, hztop⟩
    change dist z zc ≤ 1 / 4 at hzball
    rw [dist_eq_parabolicDist, parabolicDist] at hzball
    change z.1 ∈ vec3Ball 0 1 ∧ z.2 ∈ Ioc (-1) 0
    constructor
    · change vec3EuclideanNorm (z.1 - 0) < 1
      have hspace : vec3EuclideanNorm (z.1 - 0) ≤ 1 / 4 :=
        (max_le_iff.mp hzball).1
      exact hspace.trans_lt (by norm_num)
    · have htime : Real.sqrt |z.2 - (-(1 / 2 : ℝ))| ≤ 1 / 4 :=
        (max_le_iff.mp hzball).2
      have hsq : |z.2 - (-(1 / 2 : ℝ))| ≤ (1 / 4 : ℝ) ^ 2 := by
        have hnonneg : 0 ≤ Real.sqrt |z.2 - (-(1 / 2 : ℝ))| := Real.sqrt_nonneg _
        nlinarith only [htime, hnonneg,
          Real.sq_sqrt (abs_nonneg (z.2 - (-(1 / 2 : ℝ))))]
      rw [Set.mem_Ioc]
      constructor
      · have habs := abs_le.mp hsq
        linarith only [habs.1]
      · change z.2 ≤ -(1 / 2 : ℝ) at hztop
        linarith only [hztop]
  · simp [goodPointEnergy, vec3EuclideanNorm_zero]
    positivity

end ESS
