/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalParameters

/-!
# Quantitative inequalities for the complete Sobolev lifespan

The chosen lifespan makes the Abel contribution fit the fixed-point
ball and gives a strict contraction factor.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

private theorem regularisedBesselLocal_abelfactor_le_coefficient
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    regularisedBesselTensorConstant ρ ε hε k /
      Real.sqrt (2 * Real.exp 1) ≤
    regularisedBesselLocalCoefficient ρ ε hε k := by
  have hC := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
  have hS : 1 ≤ Real.sqrt (2 * Real.exp 1) := by
    apply Real.one_le_sqrt.mpr
    have he : 1 ≤ Real.exp 1 := by
      have hh := Real.add_one_le_exp (1 : ℝ)
      linarith only [hh]
    linarith only [he]
  have hSpos : 0 < Real.sqrt (2 * Real.exp 1) := by positivity
  apply (div_le_iff₀ hSpos).2
  have hA := regularisedBesselLocalCoefficient_pos ρ ε hε k
  calc
    regularisedBesselTensorConstant ρ ε hε k ≤
        regularisedBesselLocalCoefficient ρ ε hε k := by
          unfold regularisedBesselLocalCoefficient
          linarith only []
    _ ≤ regularisedBesselLocalCoefficient ρ ε hε k *
        Real.sqrt (2 * Real.exp 1) := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hS hA.le)

/-- The Abel bound of the local map fits inside the chosen H²ᵏ ball. -/
theorem regularisedBesselLocalLifespan_ball_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :
    ‖b‖ +
      2 * (regularisedBesselTensorConstant ρ ε hε k /
        Real.sqrt (2 * Real.exp 1)) *
        (regularisedBesselLocalRadius k b) ^ 2 *
        Real.sqrt (regularisedBesselLocalLifespan ρ ε hε k b) ≤
      regularisedBesselLocalRadius k b := by
  let A := regularisedBesselLocalCoefficient ρ ε hε k
  let M := 1 + ‖b‖
  have hA : 0 < A := regularisedBesselLocalCoefficient_pos ρ ε hε k
  have hM : 0 < M := by dsimp [M]; positivity
  have hAM : 0 < 16 * A * M := by positivity
  have hC := regularisedBesselLocal_abelfactor_le_coefficient ρ ε hε k
  have hδ : 0 ≤ (16 * A * M)⁻¹ := le_of_lt (inv_pos.mpr hAM)
  rw [regularisedBesselLocalLifespan_sqrt]
  change ‖b‖ + 2 *
    (regularisedBesselTensorConstant ρ ε hε k /
      Real.sqrt (2 * Real.exp 1)) * (2 * M) ^ 2 *
      (16 * A * M)⁻¹ ≤ 2 * M
  have hterm : 2 *
      (regularisedBesselTensorConstant ρ ε hε k /
        Real.sqrt (2 * Real.exp 1)) * (2 * M) ^ 2 *
        (16 * A * M)⁻¹ ≤ M / 2 := by
    calc
      _ ≤ 2 * A * (2 * M) ^ 2 * (16 * A * M)⁻¹ := by
        gcongr
      _ = M / 2 := by
        field_simp
        ring
  have hnorm : ‖b‖ ≤ M := by dsimp [M]; linarith only []
  linarith only [hterm, hnorm, hM]

/-- The Abel difference bound gives contraction factor at most one half. -/
theorem regularisedBesselLocalLifespan_contraction_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :
    2 * (regularisedBesselTensorConstant ρ ε hε k /
      Real.sqrt (2 * Real.exp 1)) *
      (2 * regularisedBesselLocalRadius k b) *
      Real.sqrt (regularisedBesselLocalLifespan ρ ε hε k b) ≤
      (1 / 2 : ℝ) := by
  let A := regularisedBesselLocalCoefficient ρ ε hε k
  let M := 1 + ‖b‖
  have hA : 0 < A := regularisedBesselLocalCoefficient_pos ρ ε hε k
  have hM : 0 < M := by dsimp [M]; positivity
  have hAM : 0 < 16 * A * M := by positivity
  have hC := regularisedBesselLocal_abelfactor_le_coefficient ρ ε hε k
  rw [regularisedBesselLocalLifespan_sqrt]
  change 2 * (regularisedBesselTensorConstant ρ ε hε k /
      Real.sqrt (2 * Real.exp 1)) * (2 * (2 * M)) *
      (16 * A * M)⁻¹ ≤ 1 / 2
  calc
    _ ≤ 2 * A * (2 * (2 * M)) * (16 * A * M)⁻¹ := by
      gcongr
    _ = 1 / 2 := by
      field_simp
      ring

end CKN.Leray

end
