/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelEnergyBound
public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelSourceOperator

/-!
# Uniform smooth-kernel bounds in the actual joint source norm

One fixed finite constant controls all translated cutoff boxes. A bound
on derivatives through order two on that box supplies the actual field
and momentum operator bounds. In particular this applies directly to
smooth polynomial increments, without any regional source inverse.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Set Metric
open scoped SchwartzMap

/-- Joint cutoff second order bound defined as `1 + jointCutoffDerivativeBound 0 + 2 *
jointCutoffDerivativeBound 1 + jointCutoffDerivativeBound 2`. -/
def jointCutoffSecondOrderBound : ℝ :=
  1 + jointCutoffDerivativeBound 0 + 2 * jointCutoffDerivativeBound 1 + jointCutoffDerivativeBound 2

theorem jointCutoffSecondOrderBound_pos : 0 < jointCutoffSecondOrderBound := by
  have h0 := jointCutoffDerivativeBound_nonneg 0
  have h1 := jointCutoffDerivativeBound_nonneg 1
  have h2 := jointCutoffDerivativeBound_nonneg 2
  unfold jointCutoffSecondOrderBound
  linarith

private theorem jointCutoff_binomial_sum_le {n : ℕ} (hn : n ≤ 2) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * jointCutoffDerivativeBound i) ≤
      jointCutoffSecondOrderBound := by
  have h0 := jointCutoffDerivativeBound_nonneg 0
  have h1 := jointCutoffDerivativeBound_nonneg 1
  have h2 := jointCutoffDerivativeBound_nonneg 2
  unfold jointCutoffSecondOrderBound
  interval_cases n <;> simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.choose_self, Nat.cast_one,
    Nat.cast_ofNat, Nat.choose_one_right, zero_add, one_mul] <;> nlinarith

theorem norm_iteratedFDeriv_cutOff_le_uniform {M : ℝ} (hM : 0 ≤ M)
    (a b : EuclideanSpace ℝ (Fin 3)) (H : JointKernelSpace → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hbound : ∀ n ≤ 2, ∀ x ∈ jointKernelBox a b 2, ‖iteratedFDeriv ℝ n H x‖ ≤ M)
    {n : ℕ} (hn : n ≤ 2) {x : JointKernelSpace} (hx : x ∈ jointKernelBox a b 2) :
    ‖iteratedFDeriv ℝ n (cutOffJointSmoothKernel a b H hH) x‖ ≤
      jointCutoffSecondOrderBound * M := by
  apply (norm_iteratedFDeriv_cutOffJointSmoothKernel_le a b H hH n x).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * jointCutoffDerivativeBound i * M := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hbound (n - i) (by omega) x hx)
        (mul_nonneg (Nat.cast_nonneg _) (jointCutoffDerivativeBound_nonneg i))
    _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * jointCutoffDerivativeBound i) * M :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (jointCutoff_binomial_sum_le hn) hM

theorem tsupport_cutOffJointSmoothKernel_subset (a b : EuclideanSpace ℝ (Fin 3))
    (H : JointKernelSpace → ℂ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    tsupport (cutOffJointSmoothKernel a b H hH) ⊆ jointKernelBox a b 2 :=
  tsupport_mul_subset_left.trans (tsupport_jointSmoothCutoff_subset a b)

theorem sqrt_jointKernelEnergy_cutOff_le {M : ℝ} (hM : 0 ≤ M)
    (a b : EuclideanSpace ℝ (Fin 3)) (H : JointKernelSpace → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hbound : ∀ n ≤ 2, ∀ x ∈ jointKernelBox a b 2, ‖iteratedFDeriv ℝ n H x‖ ≤ M) :
    Real.sqrt (jointKernelDerivativeEnergy (cutOffJointSmoothKernel a b H hH)) ≤
      4 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound * M := by
  have he := jointKernelDerivativeEnergy_le
    (mul_nonneg jointCutoffSecondOrderBound_pos.le hM) a b
    (cutOffJointSmoothKernel a b H hH) (tsupport_cutOffJointSmoothKernel_subset a b H hH)
    (fun n hn x hx => norm_iteratedFDeriv_cutOff_le_uniform hM a b H hH hbound hn hx)
  have hD := jointCutoffSecondOrderBound_pos.le
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ 16 * jointKernelBoxVolume * (jointCutoffSecondOrderBound * M) ^ 2 := he
    _ = (4 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound * M) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt jointKernelBoxVolume_nonneg]
      ring

/-- Joint smooth kernel universal constant given by `1 + 16 * Real.sqrt jointKernelBoxVolume *
jointCutoffSecondOrderBound`. -/
def jointSmoothKernelUniversalConstant : ℝ :=
  1 + 16 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound

theorem jointSmoothKernelUniversalConstant_pos : 0 < jointSmoothKernelUniversalConstant := by
  have hD := jointCutoffSecondOrderBound_pos.le
  unfold jointSmoothKernelUniversalConstant
  positivity

/-- A single actual constant controls both source components, uniformly
in the centers, separation, mass and original compact test sources. -/
theorem jointSmoothKernel_uniform_operator_bounds {μ M : ℝ} (hμ : 0 < μ) (hM : 0 ≤ M)
    (a b : EuclideanSpace ℝ (Fin 3)) (H : JointKernelSpace → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hbound : ∀ n ≤ 2, ∀ x ∈ jointKernelBox a b 2, ‖iteratedFDeriv ℝ n H x‖ ≤ M) :
    ‖jointFieldKernelOperator hμ (ball a 1 ∪ ball b 1) (cutOffJointSmoothKernel a b H hH)‖ ≤
        jointSmoothKernelUniversalConstant * max 1 μ * M ∧
      ‖jointMomentumKernelOperator hμ a b (cutOffJointSmoothKernel a b H hH)‖ ≤
        jointSmoothKernelUniversalConstant * M := by
  have hs := sqrt_jointKernelEnergy_cutOff_le hM a b H hH hbound
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
  · apply (norm_jointFieldKernelOperator_le hμ _ _).trans
    calc
      _ ≤ (2 * max 1 μ) *
          (4 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound * M) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ jointSmoothKernelUniversalConstant * max 1 μ * M := by
        have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hMμ) hM
        convert hh using 1; ring
  · apply (norm_jointMomentumKernelOperator_le hμ a b _).trans
    calc
      _ ≤ 4 * (4 * Real.sqrt jointKernelBoxVolume * jointCutoffSecondOrderBound * M) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ ≤ jointSmoothKernelUniversalConstant * M := by
        have hh := mul_le_mul_of_nonneg_right h4 hM
        convert hh using 1; ring

end VacuumBellSeparation
