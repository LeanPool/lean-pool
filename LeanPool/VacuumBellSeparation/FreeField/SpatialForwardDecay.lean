/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialSourceReserveEstimate

/-!
# Literal mass-uniform forward decay for unit balls

The threshold is exactly the three geometric requirements of Section 6.
The true source-series bound is reduced to s^(-2), uniformly in positive
mass, by the already proved scalar exponential envelope.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian

/-- Source forward kappa given by `2 * sourceMomentLambda b + 8 * Real.sqrt 3 * sourceMomentBase
b`. -/
def sourceForwardKappa (b : ℝ) : ℝ :=
  2 * sourceMomentLambda b + 8 * Real.sqrt 3 * sourceMomentBase b

/-- Source forward threshold given by `max 4 (max (16 * Real.sqrt 3 * sourceMomentBase b) (2 *
sourceForwardKappa b))`. -/
def sourceForwardThreshold (b : ℝ) : ℝ :=
  max 4 (max (16 * Real.sqrt 3 * sourceMomentBase b) (2 * sourceForwardKappa b))

/-- Source forward envelope constant given by `64 * (6 + 128) * 256 * C ^ 2`. -/
def sourceForwardEnvelopeConstant (C : ℝ) : ℝ := 64 * (6 + 128) * 256 * C ^ 2

theorem spatial_forward_polynomial_exponential {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (1 + x) * Real.exp (-x / 2) ≤ 256 ∧
      (1 + x) * Real.sqrt (1 + x) * Real.exp (-x / 2) ≤ 256 := by
  have hsq : Real.sqrt (1 + x) ≤ 1 + x := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + x by positivity), Real.sqrt_nonneg (1 + x)]
  have he : Real.exp (-x / 2) ≤ Real.exp (-x / 8) :=
    Real.exp_le_exp.mpr (by linarith)
  have hp := spatial_polynomial_exp_bound hx
  constructor
  · apply (mul_le_mul hsq he (Real.exp_nonneg _) (by positivity)).trans
    exact (mul_le_mul_of_nonneg_right (by nlinarith : 1 + x ≤ (1 + x) ^ 2)
      (Real.exp_nonneg _)).trans hp
  · apply (mul_le_mul
      (mul_le_mul_of_nonneg_left hsq (by positivity)) he
      (Real.exp_nonneg _) (by positivity)).trans
    simpa only [pow_two] using hp

theorem spatialSourceFactorBound_one_eq (C b m s : ℝ) :
    spatialSourceFactorBound C b m s 1 =
      C ^ 2 * Real.exp (sourceForwardKappa b * m - m * s) *
        (384 * Real.sqrt (1 + m * s) / (s ^ 2 * (1 + m) ^ 2) +
          8192 * (1 + m * s) * Real.sqrt (1 + m * s) / (s ^ 4 * (1 + m) ^ 4)) := by
  have he : Real.exp (-m * s + 4 * m * Real.sqrt 3 * (2 * sourceMomentBase b)) *
      Real.exp (sourceMomentLambda b * m) ^ 2 =
        Real.exp (sourceForwardKappa b * m - m * s) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold sourceForwardKappa
    ring
  unfold spatialSourceFactorBound sourceFieldMomentEnvelope sourceMomentumMomentEnvelope
    spatialFieldPolydiscBound spatialMomentumPolydiscBound
  simp only [mul_one, one_pow, mul_pow, div_pow]
  calc
    _ = C ^ 2 *
        (Real.exp (-m * s + 4 * m * Real.sqrt 3 * (2 * sourceMomentBase b)) *
          Real.exp (sourceMomentLambda b * m) ^ 2) *
        (384 * Real.sqrt (1 + m * s) / (s ^ 2 * (1 + m) ^ 2) +
          8192 * (1 + m * s) * Real.sqrt (1 + m * s) / (s ^ 4 * (1 + m) ^ 4))
            := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ = _ := by rw [he]

theorem spatialSourceFactorBound_one_le {C b m s : ℝ}
    (hm : 0 < m) (hs : sourceForwardThreshold b ≤ s) :
    spatialSourceFactorBound C b m s 1 ≤ sourceForwardEnvelopeConstant C / s ^ 2 := by
  have hs4 : 4 ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 < s := by linarith
  have hk : 2 * sourceForwardKappa b ≤ s :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  have hx : 0 ≤ m * s := by positivity
  have he : Real.exp (sourceForwardKappa b * m - m * s) ≤ Real.exp (-(m * s) / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hk hm.le]
  obtain ⟨hf, hp⟩ := spatial_forward_polynomial_exponential hx
  have hfield : Real.sqrt (1 + m * s) * Real.exp (sourceForwardKappa b * m - m * s) ≤ 256 :=
    (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)).trans hf
  have hmom : (1 + m * s) * Real.sqrt (1 + m * s) *
      Real.exp (sourceForwardKappa b * m - m * s) ≤ 256 :=
    (mul_le_mul_of_nonneg_left he (by positivity)).trans hp
  have hd2 : 1 ≤ (1 + m) ^ 2 := by nlinarith
  have hd4 : 1 ≤ (1 + m) ^ 4 := by nlinarith [sq_nonneg ((1 + m) ^ 2 - 1)]
  have hs24 : s ^ 2 ≤ s ^ 4 := by nlinarith [sq_nonneg (s ^ 2 - 1)]
  rw [spatialSourceFactorBound_one_eq]
  calc
    _ = (384 * C ^ 2 / s ^ 2) *
        ((Real.sqrt (1 + m * s) * Real.exp (sourceForwardKappa b * m - m * s)) / (1 + m) ^ 2) +
        (8192 * C ^ 2 / s ^ 4) *
        (((1 + m * s) * Real.sqrt (1 + m * s) *
          Real.exp (sourceForwardKappa b * m - m * s)) / (1 + m) ^ 4)
            := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ (384 * C ^ 2 / s ^ 2) * 256 + (8192 * C ^ 2 / s ^ 4) * 256 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left ((div_le_self (by positivity) hd2).trans hfield) (by positivity))
        (mul_le_mul_of_nonneg_left ((div_le_self (by positivity) hd4).trans hmom) (by positivity))
    _ ≤ (384 * C ^ 2 / s ^ 2) * 256 + (8192 * C ^ 2 / s ^ 2) * 256 := by
      exact _root_.add_le_add_right (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hs24) (by norm_num)) _
    _ = _ := by unfold sourceForwardEnvelopeConstant; ring

end VacuumBellSeparation
