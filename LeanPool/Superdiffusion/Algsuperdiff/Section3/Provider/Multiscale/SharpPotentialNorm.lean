/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpMeanWaveBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.PayloadSandwich

/-!
# SharpPotentialNorm

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Affine
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

theorem probe_purePotentialCoordinateQuadratic_eq
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) {sigma : ℝ} (hsigma : 0 < sigma)
    (j : Fin d) :
    blockVecDot (((Real.sqrt sigma)⁻¹ • basisVec j, 0) : BlockVec d)
        (blockMatVecMul (Ch02.coarseBlockMatrix U a)
          ((Real.sqrt sigma)⁻¹ • basisVec j, 0)) =
      sigma⁻¹ * Ch02.bCoarse U a j j := by
  have hsqrt : Real.sqrt sigma ≠ 0 := (Real.sqrt_pos.2 hsigma).ne'
  have hc : (Real.sqrt sigma)⁻¹ * (Real.sqrt sigma)⁻¹ = sigma⁻¹ := by
    field_simp [hsqrt]
    rw [Real.sq_sqrt hsigma.le]
  simp only [blockVecDot, blockMatVecMul, matVecMul_zero,
    add_zero, vecDot_zero_left, vecDot_smul_left, vecDot_smul_right,
    matVecMul_smul, Ch02.coarseBlockMatrix_upperLeft]
  rw [vecDot_basisVec_left]
  rw [show basisVec j = Pi.single j 1 from rfl, matVecMul_single]
  simp only [mul_zero, add_zero]
  change (Real.sqrt sigma)⁻¹ * ((Real.sqrt sigma)⁻¹ * Ch02.bCoarse U a j j) = _
  rw [← mul_assoc, hc]

/-- The pure-potential half of the finite-coordinate trace reduction. -/
theorem probe_inv_mul_bCoarse_matrixNorm_le_sum_abs_purePotential
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) {sigma : ℝ} (hsigma : 0 < sigma) :
    sigma⁻¹ * Ch02.matrixNorm (Ch02.bCoarse U a) ≤
      ∑ j : Fin d,
        |blockVecDot (((Real.sqrt sigma)⁻¹ • basisVec j, 0) : BlockVec d)
          (blockMatVecMul (Ch02.coarseBlockMatrix U a)
            ((Real.sqrt sigma)⁻¹ • basisVec j, 0))| := by
  have hb := Ch02.matrixNorm_le_trace_of_posSemidef (Ch02.bCoarse U a)
    (Ch02.bCoarse_posSemidef U a)
  calc
    sigma⁻¹ * Ch02.matrixNorm (Ch02.bCoarse U a)
        ≤ sigma⁻¹ * Matrix.trace (Ch02.bCoarse U a) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hsigma.le)
    _ = ∑ j : Fin d, sigma⁻¹ * Ch02.bCoarse U a j j := by
      simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
    _ ≤ ∑ j : Fin d,
        |blockVecDot (((Real.sqrt sigma)⁻¹ • basisVec j, 0) : BlockVec d)
          (blockMatVecMul (Ch02.coarseBlockMatrix U a)
            ((Real.sqrt sigma)⁻¹ • basisVec j, 0))| := by
      apply Finset.sum_le_sum
      intro j _
      rw [probe_purePotentialCoordinateQuadratic_eq U a hsigma j]
      exact le_abs_self _

/-- The pure-potential reduction at the literal upper per-cube cutoff family. -/
theorem probe_cutoffBBlockFamily_inv_le_sum_abs_purePotential
    (M : ABKModel d) (L : ℤ) {sigma : ℝ} (hsigma : 0 < sigma)
    (R : TriadicCube d) (omega : CutoffSample d) :
    cutoffBBlockFamily M L sigma⁻¹ R omega ≤
      ∑ j : Fin d,
        |blockVecDot (((Real.sqrt sigma)⁻¹ • basisVec j, 0) : BlockVec d)
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
              ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R))
            ((Real.sqrt sigma)⁻¹ • basisVec j, 0))| := by
  have hnorm := probe_inv_mul_bCoarse_matrixNorm_le_sum_abs_purePotential
    (Ch02.cubeDomain R)
    ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R) hsigma
  rw [cutoffBBlockFamily, coarseBNormCoeffField,
    dite_eq_left (coefficientCutoff_aelocallyUniformlyElliptic M L omega)]
  rw [Ch02.coarseBMatrixNorm_eq_ofAEEq
    (coefficientCutoff_canonicalFamily_aeeq M L omega) R]
  exact hnorm


end

end Algsuperdiff.Section3.Provider.Multiscale
