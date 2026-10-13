/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SuperposedCoordinateConclusion
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.SuperposedPotentialClosure
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl

/-!
# SuperposedFluxCoordinateClosed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A local finite flux-coordinate superposed result

The lower coarse-ellipticity lane only needs the `q`-coordinates of the
coarse block matrix.  This file rebuilds that finite trace reduction directly,
without passing through the combined potential-and-flux coordinate theorem.
It then proves both local Sobolev trace conditions in the corrected superposed
conclusion.  The scale-separation and literal wave-envelope gates remain
pointwise antecedents on the same cutoff sample.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Affine

noncomputable section

variable {d : ℕ}

private theorem pureFluxCoordinateQuadratic_eq
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) {sigma : ℝ} (hsigma : 0 < sigma)
    (j : Fin d) :
    blockVecDot ((0, Real.sqrt sigma • basisVec j) : BlockVec d)
        (blockMatVecMul (Ch02.coarseBlockMatrix U a)
          (0, Real.sqrt sigma • basisVec j)) =
      sigma * Ch02.sigmaStarInvCoarse U a j j := by
  have hc : Real.sqrt sigma * Real.sqrt sigma = sigma := by
    simpa [pow_two] using Real.sq_sqrt hsigma.le
  simp only [blockVecDot, blockMatVecMul, matVecMul_zero,
    zero_add, vecDot_zero_left, vecDot_smul_left, vecDot_smul_right,
    matVecMul_smul, Ch02.coarseBlockMatrix_lowerRight]
  rw [vecDot_basisVec_left]
  rw [show basisVec j = Pi.single j 1 from rfl, matVecMul_single]
  simp only [mul_zero, zero_add]
  change Real.sqrt sigma * (Real.sqrt sigma * Ch02.sigmaStarInvCoarse U a j j) = _
  rw [← mul_assoc, hc]

/-- The weighted lower coarse-matrix norm is controlled by the finite sum of
the pure flux-coordinate quadratic forms of the full coarse block matrix. -/
theorem mul_matrixNorm_sigmaStarInvCoarse_le_sum_abs_pureFluxCoordinateQuadratics
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) {sigma : ℝ} (hsigma : 0 < sigma) :
    sigma * Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a) ≤
      ∑ j : Fin d,
        |blockVecDot ((0, Real.sqrt sigma • basisVec j) : BlockVec d)
          (blockMatVecMul (Ch02.coarseBlockMatrix U a)
            (0, Real.sqrt sigma • basisVec j))| := by
  have htrace := Ch02.matrixNorm_le_trace_of_posSemidef
    (Ch02.sigmaStarInvCoarse U a) (Ch02.sigmaStarInvCoarse_posDef U a).posSemidef
  calc
    sigma * Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a) ≤
        sigma * Matrix.trace (Ch02.sigmaStarInvCoarse U a) :=
      mul_le_mul_of_nonneg_left htrace hsigma.le
    _ = ∑ j : Fin d, sigma * Ch02.sigmaStarInvCoarse U a j j := by
      simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
    _ ≤ ∑ j : Fin d,
        |blockVecDot ((0, Real.sqrt sigma • basisVec j) : BlockVec d)
          (blockMatVecMul (Ch02.coarseBlockMatrix U a)
            (0, Real.sqrt sigma • basisVec j))| := by
      apply Finset.sum_le_sum
      intro j _
      rw [pureFluxCoordinateQuadratic_eq U a hsigma j]
      exact le_abs_self _

/-- The finite flux-coordinate superposed conclusion after proving both
Sobolev trace conditions for the full bad family.  It is simultaneous only
over `j : Fin d`; the separation and literal wave gates are unchanged. -/
theorem mul_matrixNorm_sigmaStarInvCoarse_le_sum_superposedConclusionPayload_flux_basis_closed_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) (m : ℤ) {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {i : ℤ}
    (hmi : m - 1 ≤ i) (hi : i ≤ m0) {L : ℤ} (hmL : m ≤ L)
    {eps : ℝ} (heps : 0 < eps) {t : ℝ} (ht0 : 0 ≤ t) {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta9 : 9 * beta ≤ 1)
    (hbetab : 2 * b + 2 * M.gamma + eps ≤ 2 * beta)
    (hgammaWin : 4 * (2 * M.gamma + eps) ≤ 1 - beta) {kp : ℕ}
    (hcap : 9 * (99 : ℝ) ^ d *
      (Real.exp (-(Percolation.siteRateBase d / 2 * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) +
        (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) ≤ Real.exp (-(kp : ℝ))) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (Percolation.hsepSet M m (E : ℝ) b omega).Nonempty →
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m
          (whitneyScale M m (E : ℝ) b k₀ omega) n,
        cubeSupBound Q Q.scale L omega.1 ≤
          whitneyWaveLayerScale M m
            (whitneyScale M m (E : ℝ) b k₀ omega) n L * t) →
      (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) *
          Ch02.matrixNorm
            (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain (originCube d m))
              ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn
                (originCube d m))) ≤
        ∑ j : Fin d, superposedConclusionPayload M m i L (E : ℝ) b eps t beta
          k₀ kp omega 0 (basisVec j) := by
  classical
  have hsigma : (0 : ℝ) < (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar_characterization M i).1
  have hq : ∀ j : Fin d, ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (Percolation.hsepSet M m (E : ℝ) b omega).Nonempty →
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) m
          (whitneyScale M m (E : ℝ) b k₀ omega) n,
        cubeSupBound Q Q.scale L omega.1 ≤
          whitneyWaveLayerScale M m
            (whitneyScale M m (E : ℝ) b k₀ omega) n L * t) →
      |blockVecDot
          (0, Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) • basisVec j)
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d m))
              ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn
                (originCube d m)))
            (0, Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) •
              basisVec j))| ≤
        superposedConclusionPayload M m i L (E : ℝ) b eps t beta k₀ kp omega
          0 (basisVec j) := by
    intro j
    filter_upwards
        [abs_blockVecDot_coarseBlockMatrix_originCube_le_payload_superposedDivergence_ae
          hd M hS m hb0 hb hk₀ hmi hi hmL 0 (basisVec j) heps ht0 hbeta0 hbeta9
            hbetab hgammaWin hcap]
      with omega hmain hne henv
    have hF : ∀ r : Vec d,
        Ch01.PotentialZeroTraceFieldOn (openCubeSet (originCube d m))
          (fun x => superposedCompetitorSlope m
              (whitneyScale M m (E : ℝ) b k₀ omega)
              (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega) r x - r) :=
      fun r => potentialZeroTraceFieldOn_superposedCompetitorSlope_sub_badFamily
        hb0 hb hk₀ hne r
    have hG :=
      superposedCompetitorDivergence_sub_solenoidalZeroNormalTraceFieldOn_of_forall
        hd m (whitneyScale M m (E : ℝ) b k₀ omega)
        (badFamily M m (whitneyScale M m (E : ℝ) b k₀ omega) omega)
        (Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) • basisVec j) hF
    simpa [superposedConclusionPayload] using hmain hne henv
      (hF ((Real.sqrt (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ))⁻¹ •
        (0 : Vec d))) hG
  have hqAll := MeasureTheory.ae_all_iff.mpr hq
  filter_upwards [hqAll] with omega hqOmega hne henv
  refine (mul_matrixNorm_sigmaStarInvCoarse_le_sum_abs_pureFluxCoordinateQuadratics
    (Ch02.cubeDomain (originCube d m))
    ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn (originCube d m))
    hsigma).trans ?_
  exact Finset.sum_le_sum fun j _ => hqOmega j hne henv

end

end Algsuperdiff.Section3.Provider.Multiscale
