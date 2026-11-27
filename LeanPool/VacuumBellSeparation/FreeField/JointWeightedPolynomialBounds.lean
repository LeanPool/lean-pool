/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointWeightedPolynomialFactor
public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialCombinedRange

/-!
# Actual finite-rank weighted polynomial bounds on the joint source space

All vector and coefficient estimates are discharged before the operator
family is chosen. Constants precede the mass, separation and order.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian
open scoped ENNReal

variable {μ s b : ℝ} {hμ : 0 < μ}

theorem range_jointWeightedPolynomialOperator_le (v : JointWeightedMomentFamily hμ s b)
    (F G : (Fin 6 → ℂ) → ℂ) (n : ℕ) {D : ℕ} (hD : 9 * n ≤ D) :
    (jointWeightedPolynomialOperator v F G n).toLinearMap.range ≤
      jointMomentDegreeRange (𝕜 := ℂ) v.field v.momentum D := by
  have hf := (range_jointSymmetricPolynomialOperator_le v.field (jointMidpointOriented F n)
    ((jointMidpointOriented_degree F n).trans hD)).trans
      (spatialMomentDegreeRange_le_joint_left v.field v.momentum D)
  have hg := (range_jointSymmetricPolynomialOperator_le v.momentum (jointMidpointOriented G n)
    ((jointMidpointOriented_degree G n).trans hD)).trans
      (spatialMomentDegreeRange_le_joint_right v.field v.momentum D)
  rintro _ ⟨x, rfl⟩
  exact Submodule.add_mem _ (hf ⟨x, rfl⟩) (hg ⟨x, rfl⟩)

instance finiteDimensional_range_jointWeightedPolynomialOperator
    (v : JointWeightedMomentFamily hμ s b) (F G : (Fin 6 → ℂ) → ℂ) (n : ℕ) :
    FiniteDimensional ℂ (jointWeightedPolynomialOperator v F G n).toLinearMap.range :=
  Submodule.finiteDimensional_of_le (range_jointWeightedPolynomialOperator_le v F G n le_rfl)

theorem rank_jointWeightedPolynomialOperator_le (v : JointWeightedMomentFamily hμ s b)
    (F G : (Fin 6 → ℂ) → ℂ) (n : ℕ) :
    Module.finrank ℂ (jointWeightedPolynomialOperator v F G n).toLinearMap.range ≤
      2 * (9 * n + 1) ^ 3 :=
  (Submodule.finrank_mono (range_jointWeightedPolynomialOperator_le v F G n le_rfl)).trans
    (finrank_jointMomentDegreeRange_le v.field v.momentum (9 * n))

/-- Joint weighted polynomial base defined as `jointWeightedMomentDegreeBase b ^ 9 * 314572800`. -/
def jointWeightedPolynomialBase (b : ℝ) : ℝ :=
  jointWeightedMomentDegreeBase b ^ 9 * 314572800

/-- Joint weighted polynomial scale. -/
def jointWeightedPolynomialScale (C b μ s : ℝ) : ℝ :=
  128 * (jointWeightedFieldScale C b μ s ^ 2 * jointFieldEnvelope μ s +
    jointWeightedMomentumScale C b μ s ^ 2 * jointMomentumEnvelope μ s)

theorem exists_jointWeightedPolynomialOperators {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : ℝ) (hμ : 0 < μ) (s : ℝ) (hs : 600 ≤ s),
      ∃ B : ℕ → (ComplexSourceHilbert hμ (jointSourceRegion s) →L[ℂ]
          ComplexSourceHilbert hμ (jointSourceRegion s)),
        ∀ n : ℕ, FiniteDimensional ℂ (B n).toLinearMap.range ∧
          IsCompactOperator (B n) ∧ IsSelfAdjoint (B n) ∧
          sourceReserve hμ (jointSourceRegion s) ^ b * B n * sourceReserve hμ
            (jointSourceRegion s) ^ b =
            complexify (jointPolynomialKernelOperator hμ hs n) ∧
          operatorTraceNorm (B n) ≤ ENNReal.ofReal
            (jointWeightedPolynomialScale C b μ s * jointWeightedPolynomialBase b ^ n) := by
  obtain ⟨C, hC, h⟩ := exists_jointWeightedMomentFamily hb hb1
  refine ⟨C, hC, ?_⟩
  intro μ hμ s hs
  have hs₂ : 2 ≤ s := by linarith
  have hs₀ : 0 < s := by linarith
  have hT := jointMidpointMomentRadius_pos hs₂
  obtain ⟨v, hvf, hvg⟩ := h μ hμ s hs₂
  let B := jointWeightedPolynomialOperator v (jointNormalizedFieldKernel μ s)
    (jointNormalizedMomentumKernel μ s)
  refine ⟨B, ?_⟩
  intro n
  refine ⟨inferInstance, jointWeightedPolynomialOperator_isCompactOperator _ _ _ _,
    jointWeightedPolynomialOperator_isSelfAdjoint _ _ _ _,
    jointWeightedPolynomialOperator_factor hμ hs v n, ?_⟩
  exact nuclear_jointWeightedPolynomialOperator_le v
    (by unfold jointWeightedFieldScale; positivity)
    (by unfold jointWeightedMomentumScale; positivity)
    (le_max_left _ _) (by unfold jointFieldEnvelope; positivity)
    (by unfold jointMomentumEnvelope; positivity) hvf hvg
    (jointNormalizedFieldKernel μ s) (jointNormalizedMomentumKernel μ s)
    (jointNormalizedFieldKernel_norm_le hμ hs₀) (jointNormalizedMomentumKernel_norm_le hμ hs₀) n

end VacuumBellSeparation
