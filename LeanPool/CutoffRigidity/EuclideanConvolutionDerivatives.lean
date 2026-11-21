/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanL2Mollification
public import LeanPool.CutoffRigidity.EuclideanHessianEnergy

/-! # Actual coordinate and Laplacian derivatives of smooth convolution kernels

These identities differentiate only the actual compact smooth kernel.
They impose local integrability, rather than any derivative of the input.
-/

public section

namespace CutoffRigidity

open MeasureTheory ContinuousLinearMap
open scoped Convolution

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual coordinate differentiation of convolution moves to the smooth
compact kernel, with no derivative assumption on the input. -/
theorem coordinateDerivative_convolution_kernel {k f : E → ℝ}
    (hk : ContDiff ℝ 1 k) (hkc : HasCompactSupport k) (hf : LocallyIntegrable f volume)
    (i : Fin d) (x : E) :
    coordinateDerivative i (k ⋆[lsmul ℝ ℝ, volume] f) x =
      (coordinateDerivative i k ⋆[lsmul ℝ ℝ, volume] f) x := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := lsmul ℝ ℝ
  have hd := hkc.hasFDerivAt_convolution_left L hk hf x
  have hdk : Continuous (fderiv ℝ k) := (hk.fderiv_right (m := 0) (by norm_num)).continuous
  have hInt := ((hkc.fderiv ℝ).convolutionExists_left (precompL E L) hdk hf x).integrable
  change fderiv ℝ (k ⋆[L, volume] f) x (EuclideanSpace.single i 1) = _
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hInt]
  rw [convolution_lsmul]
  rfl

/-- Actual Laplacian differentiation of convolution moves to a compact C²
kernel. The input is only locally integrable. -/
theorem euclideanLaplacian_convolution_kernel {k f : E → ℝ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hf : LocallyIntegrable f volume) (x : E) :
    euclideanLaplacian (k ⋆[lsmul ℝ ℝ, volume] f) x =
      (euclideanLaplacian k ⋆[lsmul ℝ ℝ, volume] f) x := by
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by norm_num)
  have hd (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i k)
    := c1_coordinateDerivative_of_c2 hk i
  have hdc (i : Fin d) : HasCompactSupport (coordinateDerivative i k) :=
    hkc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hddc (i : Fin d) : HasCompactSupport (coordinateDerivative i (coordinateDerivative i k)) :=
    (hdc i).fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hddcont (i : Fin d) : Continuous (coordinateDerivative i (coordinateDerivative i k)) :=
    continuous_coordinateDerivative_of_c1 (hd i) i
  have htwice (i : Fin d) :
      coordinateDerivative i (coordinateDerivative i (k ⋆[lsmul ℝ ℝ, volume] f)) x =
        (coordinateDerivative i (coordinateDerivative i k) ⋆[lsmul ℝ ℝ, volume] f) x := by
    rw [funext (coordinateDerivative_convolution_kernel hk1 hkc hf i)]
    exact coordinateDerivative_convolution_kernel (hd i) (hdc i) hf i x
  have hInt (i : Fin d) : Integrable (fun t =>
      coordinateDerivative i (coordinateDerivative i k) t * f (x - t)) volume := by
    exact ((hddc i).convolutionExists_left (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
      (hddcont i) hf x).integrable
  change (∑ i : Fin d, coordinateDerivative i (coordinateDerivative i (k ⋆[lsmul ℝ ℝ,
    volume] f)) x) = _
  simp_rw [htwice, convolution_lsmul, smul_eq_mul]
  rw [← integral_finsetSum _ (fun i _ => hInt i)]
  apply integral_congr_ae
  filter_upwards with t
  change (∑ i : Fin d, coordinateDerivative i (coordinateDerivative i k) t * f (x - t)) =
    (∑ i : Fin d, coordinateDerivative i (coordinateDerivative i k) t) * f (x - t)
  rw [Finset.sum_mul]

end CutoffRigidity
