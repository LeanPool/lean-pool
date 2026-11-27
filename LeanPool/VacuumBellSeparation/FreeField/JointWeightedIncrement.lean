/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointWeightedPolynomialEnvelope
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialIncrementSeries

/-! # Actual weighted increment factors with constants fixed before the mass -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian
open scoped ENNReal

theorem jointWeightedPolynomialBase_pos (b : ℝ) : 0 < jointWeightedPolynomialBase b := by
  unfold jointWeightedPolynomialBase jointWeightedMomentDegreeBase
  positivity

/-- Joint weighted increment envelope. -/
def jointWeightedIncrementEnvelope (C μ s : ℝ) : ℝ :=
  (67072 * C ^ 2 * (jointWeightedPolynomialBase (1 / 2) + 1)) *
    Real.exp (-μ * s / 2) *
      Real.exp (2 * sourceMomentLambda (1 / 2) * μ * jointMidpointMomentRadius s)

theorem jointWeightedIncrementEnvelope_nonneg (C μ s : ℝ) :
    0 ≤ jointWeightedIncrementEnvelope C μ s := by
  have h := jointWeightedPolynomialBase_pos (1 / 2)
  unfold jointWeightedIncrementEnvelope
  positivity

theorem exists_jointWeightedIncrements :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : ℝ) (hμ : 0 < μ) (s : ℝ) (hs : 600 ≤ s),
      ∃ B : ℕ → (ComplexSourceHilbert hμ (jointSourceRegion s) →L[ℂ]
          ComplexSourceHilbert hμ (jointSourceRegion s)),
        ∀ n : ℕ, IsCompactOperator (B n) ∧ IsSelfAdjoint (B n) ∧
          sourceReserve hμ (jointSourceRegion s) ^ (1 / 2 : ℝ) * B n *
              sourceReserve hμ (jointSourceRegion s) ^ (1 / 2 : ℝ) =
            complexify (jointPolynomialIncrement hμ hs n) ∧
          operatorTraceNorm (B n) ≤ ENNReal.ofReal
            (jointWeightedIncrementEnvelope C μ s * jointWeightedPolynomialBase (1 / 2) ^ n) := by
  obtain ⟨C, hC, h⟩ := exists_jointWeightedPolynomialOperators
    (show (1 / 2 : ℝ) ≤ 1 / 2 by rfl) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨C, hC, ?_⟩
  intro μ hμ s hs
  obtain ⟨P, hP⟩ := h μ hμ s hs
  refine ⟨fun n => P (n + 1) - P n, ?_⟩
  intro n
  have hc₀ := (hP n).2.1
  have hc₁ := (hP (n + 1)).2.1
  have ha₀ := (hP n).2.2.1
  have ha₁ := (hP (n + 1)).2.2.1
  have hf₀ := (hP n).2.2.2.1
  have hf₁ := (hP (n + 1)).2.2.2.1
  have hb₀ := (hP n).2.2.2.2
  have hb₁ := (hP (n + 1)).2.2.2.2
  refine ⟨hc₁.sub hc₀, ha₁.sub ha₀, ?_, ?_⟩
  · rw [mul_sub, sub_mul, hf₁, hf₀, ← complexify_sub_real]
    rfl
  · have hbase := (jointWeightedPolynomialBase_pos (1 / 2)).le
    have hscale : 0 ≤ jointWeightedPolynomialScale C (1 / 2) μ s := by
      have hs₀ : 0 ≤ s := by linarith
      unfold jointWeightedPolynomialScale jointFieldEnvelope jointMomentumEnvelope
      positivity
    apply (operatorTraceNorm_sub_le hc₁ hc₀ ha₁ ha₀).trans
    apply (add_le_add hb₁ hb₀).trans
    rw [← ENNReal.ofReal_add (mul_nonneg hscale (pow_nonneg hbase _))
      (mul_nonneg hscale (pow_nonneg hbase _))]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = jointWeightedPolynomialScale C (1 / 2) μ s *
          (jointWeightedPolynomialBase (1 / 2) + 1) * jointWeightedPolynomialBase (1 / 2) ^ n := by
        rw [pow_succ]
        ring
      _ ≤ (67072 * C ^ 2 * Real.exp (-μ * s / 2) *
          Real.exp (2 * sourceMomentLambda (1 / 2) * μ * jointMidpointMomentRadius s)) *
          (jointWeightedPolynomialBase (1 / 2) + 1) * jointWeightedPolynomialBase (1 / 2) ^ n := by
        gcongr
        exact jointWeightedPolynomialScale_le hμ (show 2 ≤ s by linarith)
      _ = _ := by unfold jointWeightedIncrementEnvelope; ring

end VacuumBellSeparation
