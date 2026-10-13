/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.BfaLocalLane
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SuperposedFluxCoordinateClosed

/-!
# SuperposedFluxLocalPayoff

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Local lower payoff from the finite flux-coordinate conclusion

This file transports the proved local finite `q`-coordinate result from the
centered cube to an arbitrary descendant.  The transport is simultaneous over
the countable family of cutoff indices `L : ℤ`.  It then isolates the `L`-free
flux constant and converts the resulting conditional Step-3 payoff to the
existing local `bfa` lane.

The local `hsepSet.Nonempty` and literal random-profile wave envelopes stay
explicit.  In particular, no almost-everywhere statement is promoted to a
pointwise statement, and no intersection over an uncountable load space is
taken.  The running diffusivity is used directly at `i = m - 1`; there is no
comparison with another `sigmaBar` scale.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Affine

noncomputable section

variable {d : ℕ}

/-- Exact translation covariance of the normalized one-cube lower observable
used by the payload sandwich.  The totalized coefficient-field carrier is
first identified with the literal cutoff family on both cubes. -/
theorem cutoffSigmaStarInvBlockFamily_translateCutoffSample [NeZero d]
    (M : ABKModel d) (L : ℤ) (scaling : ℝ) (R : TriadicCube d)
    (omega : CutoffSample d) :
    cutoffSigmaStarInvBlockFamily M L scaling R omega =
      cutoffSigmaStarInvBlockFamily M L scaling (originCube d R.scale)
        (translateCutoffSample (triadicCubeShift R) omega) := by
  classical
  rw [cutoffSigmaStarInvBlockFamily, cutoffSigmaStarInvBlockFamily,
    coarseSigmaStarInvNormCoeffField, coarseSigmaStarInvNormCoeffField,
    dite_eq_left (coefficientCutoff_aelocallyUniformlyElliptic M L omega),
    dite_eq_left (coefficientCutoff_aelocallyUniformlyElliptic M L
      (translateCutoffSample (triadicCubeShift R) omega)),
    Ch02.coarseSigmaStarInvMatrixNorm_eq_ofAEEq
      (coefficientCutoff_canonicalFamily_aeeq M L omega) R,
    Ch02.coarseSigmaStarInvMatrixNorm_eq_ofAEEq
      (coefficientCutoff_canonicalFamily_aeeq M L
        (translateCutoffSample (triadicCubeShift R) omega))
      (originCube d R.scale),
    BadEvents.coarseSigmaStarInvMatrixNorm_cutoff_translateCutoffSample M L
      (triadicCubeShift R) (cubeSet_eq_translateSet_originCube_of_triadicCube R) omega]

/-- On an arbitrary descendant of `originCube d m`, the finite flux payoff is
available almost surely and simultaneously for every cutoff index
`L ≥ m - 1`.  Both remaining local gates are literal predicates of the
translated sample. -/
theorem descendantInverseBlock_le_superposedFluxBasis_ae
    (hd : 2 ≤ d) (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E) {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) {k₀ : ℕ} (hk₀ : 3 ≤ k₀)
    {eps : ℝ} (heps : 0 < eps) {t : ℝ} (ht0 : 0 ≤ t) {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta9 : 9 * beta ≤ 1)
    (hbetab : 2 * b + 2 * M.gamma + eps ≤ 2 * beta)
    (hgammaWin : 4 * (2 * M.gamma + eps) ≤ 1 - beta) {kp : ℕ}
    (hcap : 9 * (99 : ℝ) ^ d *
      (Real.exp (-(siteRateBase d / 2 * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) +
        (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) ≤ Real.exp (-(kp : ℝ))) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (hsepSet M R.scale (E : ℝ) b
        (translateCutoffSample (triadicCubeShift R) omega)).Nonempty →
      ∀ (L : ℤ), m - 1 ≤ L →
        (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) R.scale
            (whitneyScale M R.scale (E : ℝ) b k₀
              (translateCutoffSample (triadicCubeShift R) omega)) n,
          cubeSupBound Q Q.scale L
              (translateCutoffSample (triadicCubeShift R) omega).1 ≤
            whitneyWaveLayerScale M R.scale
              (whitneyScale M R.scale (E : ℝ) b k₀
                (translateCutoffSample (triadicCubeShift R) omega)) n L * t) →
        cutoffSigmaStarInvBlockFamily M L
            (Algsuperdiff.Section3.Annealed.sigmaBar M (m - 1) : ℝ) R omega ≤
          ∑ j : Fin d,
            superposedConclusionPayload M R.scale (m - 1) L (E : ℝ) b eps t beta
              k₀ kp (translateCutoffSample (triadicCubeShift R) omega)
              0 (basisVec j) := by
  let : NeZero d := neZeroOfModel M
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hmi : R.scale - 1 ≤ m - 1 := by
    rw [hscale]
    omega
  have hRle : R.scale ≤ m - 1 := by
    rw [hscale]
    omega
  have hcentered : ∀ (L : ℤ), ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      m - 1 ≤ L →
      (hsepSet M R.scale (E : ℝ) b omega).Nonempty →
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) R.scale
          (whitneyScale M R.scale (E : ℝ) b k₀ omega) n,
        cubeSupBound Q Q.scale L omega.1 ≤
          whitneyWaveLayerScale M R.scale
            (whitneyScale M R.scale (E : ℝ) b k₀ omega) n L * t) →
      cutoffSigmaStarInvBlockFamily M L
          (Algsuperdiff.Section3.Annealed.sigmaBar M (m - 1) : ℝ)
          (originCube d R.scale) omega ≤
        ∑ j : Fin d,
          superposedConclusionPayload M R.scale (m - 1) L (E : ℝ) b eps t beta
            k₀ kp omega 0 (basisVec j) := by
    intro L
    by_cases hmL : m - 1 ≤ L
    · filter_upwards
          [coarseInverseMatrixNorm_le_superposedFluxBasis_ae
            hd M hS R.scale hb0 hb hk₀ hmi le_rfl (hRle.trans hmL) heps ht0
              hbeta0 hbeta9 hbetab hgammaWin hcap]
        with omega hmain _ hne henv
      simpa [cutoffSigmaStarInvBlockFamily, coarseSigmaStarInvNormCoeffField,
        coefficientCutoff_aelocallyUniformlyElliptic,
        Ch02.coarseSigmaStarInvMatrixNorm,
        coefficientCutoffTriadicCoeffFamily] using! hmain hne henv
    · filter_upwards [] with omega
      intro hfalse
      exact (hmL hfalse).elim
  have hcenteredAll : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ (L : ℤ), m - 1 ≤ L →
      (hsepSet M R.scale (E : ℝ) b omega).Nonempty →
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) R.scale
          (whitneyScale M R.scale (E : ℝ) b k₀ omega) n,
        cubeSupBound Q Q.scale L omega.1 ≤
          whitneyWaveLayerScale M R.scale
            (whitneyScale M R.scale (E : ℝ) b k₀ omega) n L * t) →
      cutoffSigmaStarInvBlockFamily M L
          (Algsuperdiff.Section3.Annealed.sigmaBar M (m - 1) : ℝ)
          (originCube d R.scale) omega ≤
        ∑ j : Fin d,
          superposedConclusionPayload M R.scale (m - 1) L (E : ℝ) b eps t beta
            k₀ kp omega 0 (basisVec j) :=
    MeasureTheory.ae_all_iff.mpr hcentered
  have htranslated : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ (L : ℤ), m - 1 ≤ L →
      (hsepSet M R.scale (E : ℝ) b
        (translateCutoffSample (triadicCubeShift R) omega)).Nonempty →
      (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) R.scale
          (whitneyScale M R.scale (E : ℝ) b k₀
            (translateCutoffSample (triadicCubeShift R) omega)) n,
        cubeSupBound Q Q.scale L
            (translateCutoffSample (triadicCubeShift R) omega).1 ≤
          whitneyWaveLayerScale M R.scale
            (whitneyScale M R.scale (E : ℝ) b k₀
              (translateCutoffSample (triadicCubeShift R) omega)) n L * t) →
      cutoffSigmaStarInvBlockFamily M L
          (Algsuperdiff.Section3.Annealed.sigmaBar M (m - 1) : ℝ)
          (originCube d R.scale)
          (translateCutoffSample (triadicCubeShift R) omega) ≤
        ∑ j : Fin d,
          superposedConclusionPayload M R.scale (m - 1) L (E : ℝ) b eps t beta
            k₀ kp (translateCutoffSample (triadicCubeShift R) omega)
            0 (basisVec j) := by
    refine MeasureTheory.ae_of_ae_map
      (p := fun omega => ∀ (L : ℤ), m - 1 ≤ L →
        (hsepSet M R.scale (E : ℝ) b omega).Nonempty →
        (∀ (n : ℕ), ∀ Q ∈ whitneyLayer (d := d) R.scale
            (whitneyScale M R.scale (E : ℝ) b k₀ omega) n,
          cubeSupBound Q Q.scale L omega.1 ≤
            whitneyWaveLayerScale M R.scale
              (whitneyScale M R.scale (E : ℝ) b k₀ omega) n L * t) →
        cutoffSigmaStarInvBlockFamily M L
            (Algsuperdiff.Section3.Annealed.sigmaBar M (m - 1) : ℝ)
            (originCube d R.scale) omega ≤
          ∑ j : Fin d,
            superposedConclusionPayload M R.scale (m - 1) L (E : ℝ) b eps t beta
              k₀ kp omega 0 (basisVec j))
      (measurable_translateCutoffSample (triadicCubeShift R)).aemeasurable ?_
    rw [map_translateCutoffSample_cutoffSampleLaw]
    exact hcenteredAll
  filter_upwards [htranslated] with omega homega hne L hL henv
  rw [cutoffSigmaStarInvBlockFamily_translateCutoffSample M L
    (Algsuperdiff.Section3.Annealed.sigmaBar M (m - 1) : ℝ) R omega]
  exact homega L hL hne henv

/-! ## The `L`-free flux payload -/

/-- Sum of the finite flux-coordinate layer constants after setting the
irrelevant potential load and its wave-envelope slot to zero. -/
def superposedFluxCoordinateConst (M : ABKModel d) (n i : ℤ)
    (eps beta : ℝ) (kp : ℕ) : ℝ :=
  ∑ j : Fin d,
    layerSumConst beta (2 * M.gamma + eps) kp
      (ktotConst M n i 3 0 0 (basisVec j))
      (4 * (superposedDivConst d) ^ 2 *
        ktotConst M n i 3 0 0 (basisVec j))
      (6 * (d : ℝ))

/-- The exponent left on the random separation scale after moving the
`2 * b` collar power into the standard local lane. -/
def superposedFluxLocalExponent (M : ABKModel d) (b eps beta : ℝ) : ℝ :=
  2 * M.gamma + eps + 2 * (beta - b)

/-- The deterministic `k₀` shift absorbed into the local payoff constant. -/
def superposedFluxLocalConst (M : ABKModel d) (n i : ℤ)
    (eps beta : ℝ) (k₀ kp : ℕ) : ℝ :=
  superposedFluxCoordinateConst M n i eps beta kp *
    (3 : ℝ) ^ ((2 * M.gamma + eps + 2 * beta) * (k₀ : ℝ))

/-- The exact rare factor inherited from the corrected layer summation. -/
def superposedFluxRare (kp : ℕ) : ℝ :=
  Real.exp (-((kp : ℝ) / 36))

/-- For pure flux basis loads, both analytic layer constants are independent
of `L` and of the literal wave amplitude `t`. -/
theorem sum_superposedConclusionPayload_flux_basis_eq
    (M : ABKModel d) (n i L : ℤ) (E b eps t beta : ℝ)
    (k₀ kp : ℕ) (omega : CutoffSample d) :
    (∑ j : Fin d,
        superposedConclusionPayload M n i L E b eps t beta k₀ kp omega
          0 (basisVec j)) =
      superposedFluxCoordinateConst M n i eps beta kp *
        ((3 : ℝ) ^ ((2 * M.gamma + eps) *
            ((hsep M n E b omega + k₀ : ℕ) : ℝ)) *
          (1 + (3 : ℝ) ^
              (2 * beta * ((hsep M n E b omega + k₀ : ℕ) : ℝ)) *
            superposedFluxRare kp)) := by
  classical
  simp only [superposedConclusionPayload, superposedFluxCoordinateConst,
    superposedFluxRare, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  · simp [ktotConst, vecNormSq, vecDot]
  · simp [collarEnvelopeConst, ktotConst, vecNormSq, vecDot]

private theorem layerSumConst_nonneg_of_nonneg {b gamma : ℝ} {k₀ : ℕ}
    {Ktot Ccol Cmass : ℝ} (hKtot : 0 ≤ Ktot) (hCcol : 0 ≤ Ccol)
    (hCmass : 0 ≤ Cmass) :
    0 ≤ layerSumConst b gamma k₀ Ktot Ccol Cmass := by
  have hinv : 0 ≤ (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr three_rpow_neg_quarter_lt_one.le)
  rw [layerSumConst]
  positivity

/-- The finite flux-coordinate constant is nonnegative. -/
theorem superposedFluxCoordinateConst_nonneg (hd : 2 ≤ d)
    (M : ABKModel d) (n i : ℤ) (eps beta : ℝ) (kp : ℕ) :
    0 ≤ superposedFluxCoordinateConst M n i eps beta kp := by
  classical
  apply Finset.sum_nonneg
  intro j _
  apply layerSumConst_nonneg_of_nonneg
  · exact ktotConst_nonneg hd M n i (by norm_num) (0 : ℝ)
      (0 : Vec d) (basisVec j)
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg (superposedDivConst d)))
      (ktotConst_nonneg hd M n i (by norm_num) (0 : ℝ)
        (0 : Vec d) (basisVec j))
  · positivity


/-! ## Conditional local payoff -/


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
