/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointReverseRatio
public import LeanPool.VacuumBellSeparation.Gaussian.GeometricInterpolationMajorant
public import LeanPool.VacuumBellSeparation.Gaussian.InterpolatedReserveSeries

/-!
# The actual physical reverse reserve factor with uniform decay

The kernel difference is the original product-minus-joint covariance
operator. Its weighted and unweighted polynomial increments are derived
on that same completion; genuine interpolation and summation construct
the compact self-adjoint factor. All constants precede the mass.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian
open scoped ENNReal

theorem exists_uniform_joint_reverse_reserve_factor :
    ∃ S J : ℝ, 157286400 ≤ S ∧ 0 < J ∧
      ∀ (μ : ℝ) (hμ : 0 < μ) (s : ℝ) (hs : 600 ≤ s), S ≤ s →
        ∃ Y : ComplexSourceHilbert hμ (jointSourceRegion s) →L[ℂ]
            ComplexSourceHilbert hμ (jointSourceRegion s),
          complexify (jointDifferenceKernelOperator hμ hs) =
            sourceReserve hμ (jointSourceRegion s) ^ aRev * Y *
              sourceReserve hμ (jointSourceRegion s) ^ aRev ∧
          IsCompactOperator Y ∧ IsSelfAdjoint Y ∧
          operatorTraceNorm Y ≤ ENNReal.ofReal (J * s ^ (-gammaRev)) ∧
          operatorTraceNorm Y < ∞ := by
  obtain ⟨C, hC, hweighted⟩ := exists_jointWeightedIncrements
  obtain ⟨S, hS, hratio⟩ := exists_jointReverse_ratio_threshold
  refine ⟨S, jointReverseBoundConstant C, hS, jointReverseBoundConstant_pos hC, ?_⟩
  intro μ hμ s hs hSs
  have hsbig : 157286400 ≤ s := hS.trans hSs
  have hs₀ : 0 < s := by linarith
  have hθ : theta ∈ Set.Ioo (0 : ℝ) 1 := ⟨theta_pos_le.1, by linarith [theta_pos_le.2]⟩
  obtain ⟨B, hB⟩ := hweighted μ hμ s hs
  let A := 4000 * jointPolynomialErrorConstant * jointCommonEnvelope μ s
  let W := jointWeightedIncrementEnvelope C μ s
  let q := 78643200 / s
  let t := jointWeightedPolynomialBase (1 / 2)
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by norm_num) jointPolynomialErrorConstant_pos.le)
    (jointCommonEnvelope_nonneg μ s)
  have hW : 0 ≤ W := jointWeightedIncrementEnvelope_nonneg C μ s
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have ht : 0 ≤ t := (jointWeightedPolynomialBase_pos _).le
  have hsum := tsum_cubic_geometric_interpolation_le hA hW hq ht
    ⟨hθ.1.le, hθ.2.le⟩ (hratio s hSs)
  have hsumfin : (∑' n : ℕ,
      ENNReal.ofReal (A * ((n : ℝ) + 1) ^ 3 * q ^ n) ^ (1 - theta) *
        ENNReal.ofReal (W * t ^ n) ^ theta) < ∞ := hsum.trans_lt ENNReal.ofReal_lt_top
  have htrace (n : ℕ) : operatorTraceNorm (B n) < ∞ :=
    (hB n).2.2.2.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨Y, hf, hc, ha, hn, hfin⟩ := exists_reserve_factor_of_interpolated_majorants
    (sourceReserve_nonneg hμ (jointSourceRegion s))
    (fun n => (hB n).1) (fun n => (hB n).2.1) htrace
    (fun n => (hB n).2.2.1) (hasSum_complexified_jointPolynomialIncrement hμ hsbig) hθ
    (fun n => ENNReal.ofReal (A * ((n : ℝ) + 1) ^ 3 * q ^ n))
    (fun n => ENNReal.ofReal (W * t ^ n))
    (nuclear_jointPolynomialIncrement_cubic hμ hsbig) (fun n => (hB n).2.2.2) hsumfin
  refine ⟨Y, hf, hc, ha, ?_, hfin⟩
  exact (hn.trans hsum).trans (ENNReal.ofReal_le_ofReal
    (jointReverse_envelope_le hμ (show 4 ≤ s by linarith)))

end VacuumBellSeparation
