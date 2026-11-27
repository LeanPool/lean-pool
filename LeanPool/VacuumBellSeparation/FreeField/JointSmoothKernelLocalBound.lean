/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelLocalCutoff

/-!
# Uniform operators from locally smooth kernel patches

The cutoff centers and the total source region are independent. This
allows all four patches to act on the same joint-source completion.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Set Metric
open scoped SchwartzMap

theorem sqrt_jointKernelEnergy_cutOffLocal_le {M : ℝ} (hM : 0 ≤ M)
    (a b : EuclideanSpace ℝ (Fin 3)) (H : JointKernelSpace → ℂ)
    (O : Set JointKernelSpace) (hO : IsOpen O) (hbox : jointKernelBox a b 2 ⊆ O)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H O)
    (hbound : ∀ n ≤ 2, ∀ x ∈ jointKernelBox a b 2, ‖iteratedFDeriv ℝ n H x‖ ≤ M) :
    Real.sqrt (jointKernelDerivativeEnergy (cutOffJointLocalKernel a b H O hO hbox hH)) ≤
      4 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound * M := by
  have hD := jointCutoffSecondOrderBound_pos.le
  have he := jointKernelDerivativeEnergy_le (mul_nonneg hD hM) a b
    (cutOffJointLocalKernel a b H O hO hbox hH)
    (tsupport_cutOffJointLocalKernel_subset a b H O hO hbox hH)
    (fun n hn x hx => norm_iteratedFDeriv_cutOffLocal_le_uniform hM a b H O hO hbox hH hbound hn hx)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ 16 * jointKernelBoxVolume * (jointCutoffSecondOrderBound * M) ^ 2 := he
    _ = (4 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound * M) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt jointKernelBoxVolume_nonneg]
      ring

/-- The same positive constant controls locally smooth patches in the
original total-source norm, including diagonal and off-diagonal patches. -/
theorem jointLocalKernel_uniform_operator_bounds {μ M : ℝ} (hμ : 0 < μ) (hM : 0 ≤ M)
    (a b p q : EuclideanSpace ℝ (Fin 3)) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (H : JointKernelSpace → ℂ) (O : Set JointKernelSpace) (hO : IsOpen O)
    (hbox : jointKernelBox a b 2 ⊆ O) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H O)
    (hbound : ∀ n ≤ 2, ∀ x ∈ jointKernelBox a b 2, ‖iteratedFDeriv ℝ n H x‖ ≤ M) :
    ‖jointFieldKernelOperator hμ U (cutOffJointLocalKernel a b H O hO hbox hH)‖ ≤
        jointSmoothKernelUniversalConstant * max 1 μ * M ∧
      ‖jointMomentumKernelOperator hμ p q (cutOffJointLocalKernel a b H O hO hbox hH)‖ ≤
        jointSmoothKernelUniversalConstant * M := by
  have hs := sqrt_jointKernelEnergy_cutOffLocal_le hM a b H O hO hbox hH hbound
  have hD := jointCutoffSecondOrderBound_pos.le
  have hc : 0 ≤ 4 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound := by positivity
  have h2 : 2 * (4 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound) ≤
      jointSmoothKernelUniversalConstant := by
    unfold jointSmoothKernelUniversalConstant
    nlinarith
  have h4 : 4 * (4 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound) ≤
      jointSmoothKernelUniversalConstant := by
    unfold jointSmoothKernelUniversalConstant
    linarith
  have hMμ : 0 ≤ max 1 μ := by positivity
  constructor
  · apply (norm_jointFieldKernelOperator_le hμ U _).trans
    calc
      _ ≤ (2 * max 1 μ) *
          (4 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound * M) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ jointSmoothKernelUniversalConstant * max 1 μ * M := by
        have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hMμ) hM
        convert hh using 1; ring
  · apply (norm_jointMomentumKernelOperator_le hμ p q _).trans
    calc
      _ ≤ 4 * (4 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound * M) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ ≤ jointSmoothKernelUniversalConstant * M := by
        have hh := mul_le_mul_of_nonneg_right h4 hM
        convert hh using 1; ring

end VacuumBellSeparation
