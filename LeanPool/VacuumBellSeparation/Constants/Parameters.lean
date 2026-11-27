/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Constants.ParameterDefs
public import LeanPool.VacuumBellSeparation.Probability.Exponents
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Numerical parameters of Sections 7 and 8

The fixed parameters of the manuscript, equations `eq:reverse-exponents` (7.10),
`eq:orders` (8.1) and `eq:completion-exponents` (8.15), together with the elementary
arithmetic facts asserted about them, and two scalar bounds used in the proof of
Theorem 7.2 and in (8.13).

These are statements about explicit real numbers only; they involve no field-theoretic
content.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem theta_eq : theta = 1 / 2 ^ 17 := by
  norm_num [theta, Lambda0]

theorem aRev_eq : aRev = 1 / 2 ^ 18 := by
  norm_num [aRev, theta, Lambda0]

theorem gammaRev_eq : gammaRev = 2 * (1 - 1 / 2 ^ 17) := by
  norm_num [gammaRev, theta, Lambda0]

/-- `0 < θ ≤ 1/64`, as stated after (7.10). -/
theorem theta_pos_le : 0 < theta ∧ theta ≤ 1 / 64 := by
  constructor <;> norm_num [theta, Lambda0]

/-- `0 < a ≤ 1/8`, as stated after (7.10). -/
theorem aRev_pos_le : 0 < aRev ∧ aRev ≤ 1 / 8 := by
  constructor <;> norm_num [aRev, theta, Lambda0]

/-- `γ > 0`, as stated after (7.10). -/
theorem gammaRev_pos : 0 < gammaRev := by
  norm_num [gammaRev, theta, Lambda0]

/-- `4/a = 2²⁰` exactly, so `r₊ = ⌈4/a⌉ = 4/a`. -/
theorem four_div_aRev : 4 / aRev = rPlus := by
  norm_num [aRev, theta, Lambda0, rPlus]

/-- `a r₊ = 4`, as stated after (8.1). -/
theorem aRev_mul_rPlus : aRev * rPlus = 4 := by
  norm_num [aRev, theta, Lambda0, rPlus]

theorem rMinus_eq : rMinus = 2 ^ 18 / (2 ^ 18 - 1) := by
  norm_num [rMinus, aRev, theta, Lambda0]

/-- `1 < r₋ < 2`, as stated after (8.1). -/
theorem one_lt_rMinus_lt_two : 1 < rMinus ∧ rMinus < 2 := by
  constructor <;> norm_num [rMinus, aRev, theta, Lambda0]

/-- `r₊ ≥ 32`, as stated after (8.1); in particular `r₊ > 2`. -/
theorem rPlus_ge : 32 ≤ rPlus ∧ 2 < rPlus := by
  constructor <;> norm_num [rPlus]

/-- The exponent `a` of (3.2) at the order `r₋` is the reverse exponent `a` of (7.10). -/
theorem expA_rMinus : expA rMinus = aRev := by
  norm_num [expA, rMinus, aRev, theta, Lambda0]

/-- `b = 1 - 1/r₊ = 1 - 2⁻²⁰`, (8.1). -/
theorem expB_rPlus : expB rPlus = 1 - 1 / 2 ^ 20 := by
  norm_num [expB, rPlus]

/-- `η = 1 - 1/(4b²)`, (8.15). -/
theorem expEta_eq : expEta rPlus rMinus = 1 - 1 / (4 * expB rPlus ^ 2) := by
  norm_num [expEta, expA, expB, rPlus, rMinus, aRev, theta, Lambda0]

/-- `η > 0` for the parameters of Section 8, as stated after (8.1). -/
theorem expEta_pos : 0 < expEta rPlus rMinus := by
  norm_num [expEta, expA, expB, rPlus, rMinus, aRev, theta, Lambda0]

/-- `ν₋ = 2¹⁸ - 1`, (8.15). -/
theorem nuMinus_eq : nuMinus rMinus = 2 ^ 18 - 1 := by
  norm_num [nuMinus, expA, rMinus, aRev, theta, Lambda0]

/-- `ν₊ = (1 + b)/(4b²)`, (8.15). -/
theorem nuPlus_eq : nuPlus rPlus rMinus = (1 + expB rPlus) / (4 * expB rPlus ^ 2) := by
  norm_num [nuPlus, expA, expB, rPlus, rMinus, aRev, theta, Lambda0]

/-- `sup_{ξ ≥ 0} (1 + ξ)² e^{-ξ/8} ≤ 256`, used for (7.14). -/
theorem one_add_sq_mul_exp_neg_le {ξ : ℝ} (hξ : 0 ≤ ξ) :
    (1 + ξ) ^ 2 * Real.exp (-(ξ / 8)) ≤ 256 := by
  have h1 : ξ / 16 + 1 ≤ Real.exp (ξ / 16) := Real.add_one_le_exp _
  have h2 : 1 + ξ ≤ 16 * Real.exp (ξ / 16) := by linarith
  have hpos : 0 < Real.exp (ξ / 16) := Real.exp_pos _
  have h3 : Real.exp (ξ / 8) = Real.exp (ξ / 16) * Real.exp (ξ / 16) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : (1 + ξ) ^ 2 ≤ 256 * Real.exp (ξ / 8) := by
    rw [h3]
    nlinarith
  have h5 : Real.exp (-(ξ / 8)) * Real.exp (ξ / 8) = 1 := by
    rw [← Real.exp_add]
    simp
  have h6 : 0 < Real.exp (-(ξ / 8)) := Real.exp_pos _
  calc (1 + ξ) ^ 2 * Real.exp (-(ξ / 8))
      ≤ 256 * Real.exp (ξ / 8) * Real.exp (-(ξ / 8)) :=
        mul_le_mul_of_nonneg_right h4 h6.le
    _ = 256 := by
        rw [mul_assoc, mul_comm (Real.exp (ξ / 8)), h5, mul_one]

/-- `e^x - 1 ≤ 2x` for `0 ≤ x ≤ 1`, used for (8.13). -/
theorem exp_sub_one_le_two_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x - 1 ≤ 2 * x := by
  have habs : |x| ≤ 1 := abs_le.mpr ⟨by linarith, h1⟩
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le habs)).2
  nlinarith

end VacuumBellSeparation
