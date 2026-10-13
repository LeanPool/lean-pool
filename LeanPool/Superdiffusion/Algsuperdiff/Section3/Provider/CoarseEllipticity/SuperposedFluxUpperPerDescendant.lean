/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.Assembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileConstants
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanDepthChoice
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanTunedAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandConsumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandOrdinaryProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperBandMeanConsumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBaseProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperDeepBandTailConsumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperDeepBandTailOrdinaryLane
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperGoodBaseConsumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHeadSharpFrozenAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperHeadSharpSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperSaturatedBlockProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperWaveTailE12Consumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperWaveTailTraceE12Consumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedLayerNamedDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedPotentialProfile

/-!
# SuperposedFluxUpperPerDescendant

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Per-descendant upper split for the superposed flux

This module constructs the twelve analytic lanes controlling the coarse upper block on a
single descendant cube. It packages them into a deterministic contribution, an ordinary
`Gamma_1` contribution, and an exceptional contribution.

The public result `superposedFlux_upper_per_descendant_split` deliberately stops before
the depth and exponent aggregation. Its exceptional scale remains in the raw form produced
by the twelve-lane construction.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

private theorem named_layer_ennreal_bound
    {d : ℕ} (M : ABKModel d) (m : ℤ) (E : ℝ) (R : TriadicCube d)
    (j : Fin d) (n : ℕ) (omega : Cutoff.CutoffSample d) :
    let ell :=
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpLayerAnchor
        R.scale Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) n
    let headSq := fun eta =>
      Algsuperdiff.Section3.Provider.Multiscale.waveHeadTerm
        M R.scale (E : ℝ)
        Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB ell eta ^ 2
    let bandSq := fun _eta =>
      Algsuperdiff.Section3.Provider.CoarseEllipticity.waveBandMean
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.probeDeepBandMeanAmplitude d)
        M.gamma
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) ^ 2
    let deepSq := fun eta =>
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeDeepBandGaugedTail
        M (originCube d R.scale) ell
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ))
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) eta ^ 2
    let afterSq := fun eta =>
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpAfterBandTerm
        M R.scale ell
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) m eta ^ 2
    let tailSq := fun eta =>
      Algsuperdiff.Section3.Provider.Multiscale.waveTailTerm
        M R.scale (E : ℝ)
        Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
        R.scale ell eta ^ 2
    let translated :=
      Algsuperdiff.Section3.Cutoff.translateCutoffSample (triadicCubeShift R) omega
    ENNReal.ofReal
        (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedMeanLayerEnvelope
          M R.scale (E : ℝ)
          Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
            M (E : ℝ)) n (m - 1) m translated (basisVec j)
          (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)) ≤
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodBaseTerm
            d n (basisVec j)) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j) headSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j) bandSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j) deepSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j) afterSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j) tailSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarBaseTerm
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) headSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) bandSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) deepSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) afterSq translated) +
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d) tailSq translated) := by
  dsimp only
  rw [Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedMeanLayerEnvelope_eq_namedSum]
  unfold Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedLayerNamedSum
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  refine ENNReal.ofReal_add_le.trans (add_le_add_left ?_ _)
  exact ENNReal.ofReal_add_le

private theorem merge_twelve_ennreal_lanes
    {S a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : ENNReal}
    {g ho hr bo br do_ dr ao ar wb wr cb ch cband cd ca cw : ENNReal}
    (hS : S ≤ a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11)
    (h0 : a0 ≤ g) (h1 : a1 ≤ ho + hr) (h2 : a2 ≤ bo + br)
    (h3 : a3 ≤ do_ + dr) (h4 : a4 ≤ ao + ar) (h5 : a5 ≤ wb + wr)
    (h6 : a6 ≤ cb) (h7 : a7 ≤ ch) (h8 : a8 ≤ cband) (h9 : a9 ≤ cd)
    (h10 : a10 ≤ ca) (h11 : a11 ≤ cw) :
    S ≤ (g + bo) + (ho + do_ + ao) +
      (hr + br + dr + ar + wb + wr + cb + ch + cband + cd + ca + cw) := by
  calc
    S ≤ a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 := hS
    _ ≤ g + (ho + hr) + (bo + br) + (do_ + dr) + (ao + ar) + (wb + wr) +
        cb + ch + cband + cd + ca + cw := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add
              (add_le_add
                (add_le_add
                  (add_le_add
                    (add_le_add
                      (add_le_add
                        (add_le_add
                          (add_le_add h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11
    _ = _ := by ring

private theorem pack_twelve_ennreal_lanes
    {g bo ho do_ ao hr br dr ar wb wr cb ch cband cd ca cw C : ENNReal}
    (hdet : g + bo ≤ C) :
    (g + bo) + (ho + do_ + ao) +
        (hr + br + dr + ar + wb + wr + cb + ch + cband + cd + ca + cw) ≤
      C + (∑ i : Fin 3, ![ho, do_, ao] i) +
        (∑ i : Fin 12, ![hr, br, dr, ar, wb, wr, cb, ch, cband, cd, ca, cw] i) := by
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, add_assoc]
  simpa only [add_assoc] using add_le_add hdet
    (le_refl (ho + do_ + ao + hr + br + dr + ar + wb + wr + cb + ch +
      cband + cd + ca + cw))

private theorem real_three_term_of_ennreal
    {x C u v : ℝ} {S : ENNReal}
    (hC : 0 ≤ C) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hx : ENNReal.ofReal x ≤ S)
    (hS : S ≤ ENNReal.ofReal C + ENNReal.ofReal u + ENNReal.ofReal v) :
    x ≤ C + u + v := by
  have hsum : ENNReal.ofReal C + ENNReal.ofReal u + ENNReal.ofReal v =
      ENNReal.ofReal (C + u + v) := by
    calc
      _ = ENNReal.ofReal (C + u) + ENNReal.ofReal v :=
        congrArg (fun z => z + ENNReal.ofReal v) (ENNReal.ofReal_add hC hu).symm
      _ = _ := (ENNReal.ofReal_add (add_nonneg hC hu) hv).symm
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (add_nonneg hC hu) hv)).1 ((hx.trans hS).trans_eq hsum)

private theorem ae_twelve_lane_domination
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {X g ho hr bo br do_ dr ao ar wb wr cb ch cband cd ca cw Uone Uexp : Omega → ℝ}
    {C : ℝ} {S a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Omega → ENNReal}
    (hC : 0 ≤ C) (hUone0 : ∀ omega, 0 ≤ Uone omega)
    (hUexp0 : ∀ omega, 0 ≤ Uexp omega)
    (hpotential : ∀ᵐ omega ∂mu, ENNReal.ofReal (X omega) ≤ S omega)
    (hEnvelope : ∀ omega, S omega ≤
      a0 omega + a1 omega + a2 omega + a3 omega + a4 omega + a5 omega +
        a6 omega + a7 omega + a8 omega + a9 omega + a10 omega + a11 omega)
    (h0 : ∀ omega, a0 omega = ENNReal.ofReal (g omega))
    (h1 : ∀ omega, a1 omega ≤ ENNReal.ofReal (ho omega) + ENNReal.ofReal (hr omega))
    (h2 : ∀ omega, a2 omega ≤ ENNReal.ofReal (bo omega) + ENNReal.ofReal (br omega))
    (h3 : ∀ᵐ omega ∂mu, a3 omega ≤ ENNReal.ofReal (do_ omega) + ENNReal.ofReal (dr omega))
    (h4 : ∀ᵐ omega ∂mu, a4 omega ≤ ENNReal.ofReal (ao omega) + ENNReal.ofReal (ar omega))
    (h5 : ∀ᵐ omega ∂mu, a5 omega ≤ ENNReal.ofReal (wb omega) + ENNReal.ofReal (wr omega))
    (h6 : ∀ omega, a6 omega = ENNReal.ofReal (cb omega))
    (h7 : ∀ᵐ omega ∂mu, ENNReal.ofReal (ch omega) = a7 omega)
    (h8 : ∀ omega, a8 omega = ENNReal.ofReal (cband omega))
    (h9 : ∀ᵐ omega ∂mu, ENNReal.ofReal (cd omega) = a9 omega)
    (h10 : ∀ᵐ omega ∂mu, ENNReal.ofReal (ca omega) = a10 omega)
    (h11 : ∀ᵐ omega ∂mu, ENNReal.ofReal (cw omega) = a11 omega)
    (hdet : ∀ omega, ENNReal.ofReal (g omega) + ENNReal.ofReal (bo omega) ≤
      ENNReal.ofReal C)
    (hone : ∀ omega, ENNReal.ofReal (Uone omega) =
      ∑ i : Fin 3, ![ENNReal.ofReal (ho omega), ENNReal.ofReal (do_ omega),
        ENNReal.ofReal (ao omega)] i)
    (hexp : ∀ omega, ENNReal.ofReal (Uexp omega) =
      ∑ i : Fin 12, ![ENNReal.ofReal (hr omega), ENNReal.ofReal (br omega),
        ENNReal.ofReal (dr omega), ENNReal.ofReal (ar omega), ENNReal.ofReal (wb omega),
        ENNReal.ofReal (wr omega), ENNReal.ofReal (cb omega), ENNReal.ofReal (ch omega),
        ENNReal.ofReal (cband omega), ENNReal.ofReal (cd omega), ENNReal.ofReal (ca omega),
        ENNReal.ofReal (cw omega)] i) :
    ∀ᵐ omega ∂mu, X omega ≤ C + Uone omega + Uexp omega := by
  filter_upwards [hpotential, h3, h4, h5, h7, h9, h10, h11] with
    omega hpot h3' h4' h5' h7' h9' h10' h11'
  have hmerged := (merge_twelve_ennreal_lanes
    (hEnvelope omega) (h0 omega).le (h1 omega) (h2 omega) h3' h4' h5'
    (h6 omega).le h7'.symm.le (h8 omega).le h9'.symm.le h10'.symm.le
    h11'.symm.le).trans (pack_twelve_ennreal_lanes (hdet omega))
  rw [← hone omega, ← hexp omega] at hmerged
  exact real_three_term_of_ennreal hC (hUone0 omega) (hUexp0 omega)
    hpot hmerged

private theorem nonnegative_pointwise_repair
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {X Uone Uexp : Omega → ℝ} {C Aone Aexp : ℝ} {Ψone Ψexp : ℝ → ℝ}
    (hXmeas : Measurable X)
    (hUone0 : ∀ omega, 0 ≤ Uone omega) (hUoneMeas : Measurable Uone)
    (hUexp0 : ∀ omega, 0 ≤ Uexp omega) (hUexpMeas : Measurable Uexp)
    (hUoneO : HCPolySupport.IndependentSums.IsBigOWith mu Ψone Uone Aone)
    (hUexpO : HCPolySupport.IndependentSums.IsBigOWith mu Ψexp Uexp Aexp)
    (hae : ∀ᵐ omega ∂mu, X omega ≤ C + Uone omega + Uexp omega) :
    ∃ Uone' Uexp' : Omega → ℝ,
      (∀ omega, 0 ≤ Uone' omega) ∧ Measurable Uone' ∧
      (∀ omega, 0 ≤ Uexp' omega) ∧ Measurable Uexp' ∧
      (∀ omega, X omega ≤ C + Uone' omega + Uexp' omega) ∧
      HCPolySupport.IndependentSums.IsBigOWith mu Ψone Uone' Aone ∧
      HCPolySupport.IndependentSums.IsBigOWith mu Ψexp Uexp' Aexp := by
  let Uexp' : Omega → ℝ := fun omega =>
    max (Uexp omega) (X omega - C - Uone omega)
  have hUexp'0 : ∀ omega, 0 ≤ Uexp' omega := fun omega =>
    (hUexp0 omega).trans (le_max_left _ _)
  have hUexp'Meas : Measurable Uexp' :=
    hUexpMeas.max ((hXmeas.sub measurable_const).sub hUoneMeas)
  have hdom : ∀ omega, X omega ≤ C + Uone omega + Uexp' omega := by
    intro omega
    have hmax := le_max_right (Uexp omega) (X omega - C - Uone omega)
    dsimp only [Uexp']
    linarith
  have hAE : Uexp =ᵐ[mu] Uexp' := by
    filter_upwards [hae] with omega homega
    dsimp only [Uexp']
    rw [max_eq_left]
    linarith
  exact ⟨Uone, Uexp', hUone0, hUoneMeas, hUexp'0, hUexp'Meas, hdom,
    hUoneO, Algsuperdiff.Section3.Provider.Tail.isBigOWith_of_ae_eq hAE hUexpO⟩

/-- Constructs the pointwise deterministic, ordinary, and exceptional split for every
single descendant cube. The exceptional scale is left in its raw twelve-lane form for
the upper-leg aggregation layer to normalize. -/
theorem superposedFlux_upper_per_descendant_split
    {d : ℕ}
    (M : ABKModel d) (m : ℤ)
    (E : {E : ℝ // 1 ≤ E})
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    (sigma Clane : ℝ)
    (hsigma0 : 0 < sigma)
    (hsigmaHalf : sigma ≤ 1 / 2)
    (hmaxLane : max (Real.exp (Clane / sigma))
      (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hE2 : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hlanePos : 0 < Clane)
    (hgoodBaseOutput :
      Algsuperdiff.Section3.Provider.Multiscale.probeSharpGoodBaseConst d ≤ Clane)
    (hgoodHeadOutput :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.goodHeadTunedOutputConst d ≤ Clane)
    (hgoodBandOutput :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpBandMeanTunedOutputConst d ≤ Clane)
    (hgoodDeepOutput :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpDeepBandTailTunedOutputConst d ≤ Clane)
    (hgoodAfterOutput :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpAfterBandTunedOutputConst d ≤ Clane)
    (hgoodWaveOutput :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpWaveTailTunedOutputConst d ≤ Clane)
    (hcollarBaseOutput :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpCollarBaseTunedOutputConst d ≤ Clane)
    (hcollarHeadOutput :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.collarHeadTunedPerDescendantOutputConst d ≤ Clane)
    (hcollarBandOutput :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanTunedOutputConst d ≤ Clane)
    (hcollarDeepOutput :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.collarDeepTailTunedOutputConst d ≤ Clane)
    (hcollarAfterOutput :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.collarAfterBandTunedOutputConst d ≤ Clane)
    (hcollarWaveOutput :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpCollarWaveTailTunedOutputConst d ≤ Clane)
    (hprofileAuxLane :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.profileAuxiliaryConst d ≤ Clane)
    (hdepthThresholdLane :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepthThreshold d ≤ Clane)
    (hk0 : 3 ≤
      Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
        M (E : ℝ)) :
    let Cblock : ℝ :=
      (12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1) * Clane
    ∀ (k : ℕ) (R : TriadicCube d),
              R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
                ∃ Uone Uexp : Cutoff.CutoffSample d → ℝ,
                  (∀ omega, 0 ≤ Uone omega) ∧
                  Measurable Uone ∧
                  (∀ omega, 0 ≤ Uexp omega) ∧
                  Measurable Uexp ∧
                  (∀ omega,
                      Algsuperdiff.Section3.Provider.CoarseEllipticity.cutoffBBlockFamily
                          M m (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ R omega ≤
                      Cblock + Uone omega + Uexp omega) ∧
                  HCPolySupport.IndependentSums.IsBigOWith
                    (Cutoff.cutoffSampleLaw M).toMeasure
                    (HCPolySupport.IndependentSums.gammaSigma 1) Uone
                    (Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude
                      Cblock (Disorder.cstar M) M.gamma k) ∧
                  HCPolySupport.IndependentSums.IsBigOWith
                    (Cutoff.cutoffSampleLaw M).toMeasure
                    (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3)) Uexp
                    ((12 *
                        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst) *
                      ((3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) *
                        (Real.exp
                          (-(Clane⁻¹ * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) ^ 8)) := by
  let Cblock : ℝ :=
    (12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1) * Clane
  change ∀ (k : ℕ) (R : TriadicCube d),
            R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
              ∃ Uone Uexp : Cutoff.CutoffSample d → ℝ,
                (∀ omega, 0 ≤ Uone omega) ∧
                Measurable Uone ∧
                (∀ omega, 0 ≤ Uexp omega) ∧
                Measurable Uexp ∧
                (∀ omega,
                    Algsuperdiff.Section3.Provider.CoarseEllipticity.cutoffBBlockFamily
                        M m (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ R omega ≤
                    Cblock + Uone omega + Uexp omega) ∧
                HCPolySupport.IndependentSums.IsBigOWith
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma 1) Uone
                  (Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude
                    Cblock (Disorder.cstar M) M.gamma k) ∧
                HCPolySupport.IndependentSums.IsBigOWith
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3)) Uexp
                  ((12 *
                      Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst) *
                    ((3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) *
                      (Real.exp
                        (-(Clane⁻¹ * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) ^ 8))
  intro k R hR
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let : NeZero d := ⟨by omega⟩
  have hmaxAux :
      max (Real.exp
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.profileAuxiliaryConst d /
          sigma)) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmaxLane)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 hprofileAuxLane)).trans
        ((le_max_left _ _).trans hmaxLane)
  have hpotential : ∀ (k : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)) →
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          ENNReal.ofReal
              (Algsuperdiff.Section3.Provider.CoarseEllipticity.cutoffBBlockFamily
                M m (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ R omega) ≤
            ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
              (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedMeanLayerEnvelope
                M R.scale (E : ℝ)
                  Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
                  (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
                    M (E : ℝ)) n (m - 1) m
                  (Algsuperdiff.Section3.Cutoff.translateCutoffSample
                    (triadicCubeShift R) omega)
                  (basisVec j)
                  (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)) := by
    intro k R hR
    exact
      Algsuperdiff.Section3.Provider.Multiscale.ofReal_cutoffBBlockFamily_descendant_le_sharpFramedMeanEnvelope_ae_of_profileAuxiliaryMaxGate
        M hR hstate hsigma0 hsigmaHalf hmaxAux hE2 hk0 (by omega)
  obtain ⟨headOrdinary, headRare, headOrdinaryScale, headRareScale,
      hhead⟩ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.exists_good_head_tuned_finite_trace_split
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hgoodHeadOutput
  rcases hhead with
    ⟨hheadOrdinaryNonneg, hheadOrdinaryMeasurable,
      hheadRareNonneg, hheadRareMeasurable, _,
      _, hheadENNRealDom, hheadOrdinaryO,
      _, hheadOrdinaryScaleLe,
      hheadRareO, _, hheadRareScaleLe⟩
  obtain ⟨bandOrdinary, bandRare, bandRareScale, hband⟩ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.exists_good_band_mean_tuned_finite_trace_split
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hgoodBandOutput
  rcases hband with
    ⟨hbandOrdinaryNonneg, hbandOrdinaryMeasurable,
      hbandRareNonneg, hbandRareMeasurable, _,
      _, hbandENNRealDom, hbandOrdinaryLe,
      hbandRareO, _, hbandRareScaleLe⟩
  obtain ⟨deepOrdinary, deepRare, deepOrdinaryScale, deepRareScale,
      hdeep⟩ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.exists_tunedDeepBandTail_good_finite_trace_split
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2
        (max_le hprofileAuxLane hgoodDeepOutput)
  rcases hdeep with
    ⟨hdeepOrdinaryNonneg, hdeepOrdinaryMeasurable,
      hdeepRareNonneg, hdeepRareMeasurable, _,
      _, hdeepENNRealDom,
      hdeepOrdinaryO, _, hdeepOrdinaryScaleLe,
      hdeepRareO, _, hdeepRareScaleLe⟩
  obtain ⟨afterOrdinary, afterRare, afterOrdinaryScale, afterRareScale,
      hafter⟩ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.exists_tunedAfterBand_good_finite_trace_split
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hgoodAfterOutput
  rcases hafter with
    ⟨hafterOrdinaryNonneg, hafterOrdinaryMeasurable,
      hafterRareNonneg, hafterRareMeasurable, _,
      _, hafterENNRealDom, hafterOrdinaryO,
      _, hafterOrdinaryScaleLe,
      hafterRareO, _, hafterRareScaleLe⟩
  let laneX : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let laneEps : ℝ := Real.exp (-(Clane⁻¹ * laneX))
  let depthFactor : ℝ := (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1))
  let rarePerLaneScale : ℝ := depthFactor * laneEps ^ 8
  let collarBase : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseTraceLane
      M R (E : ℝ)
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ))
  let collarHead : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ j : Fin d, ∑' n : ℕ,
      Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
        M R.scale (E : ℝ)
        Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) n (m - 1) (basisVec j)
        (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)
        (fun eta => Algsuperdiff.Section3.Provider.Multiscale.waveHeadTerm
          M R.scale (E : ℝ)
          Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpLayerAnchor
            R.scale
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n) eta ^ 2)
        (Algsuperdiff.Section3.Cutoff.translateCutoffSample
          (triadicCubeShift R) omega)
  let collarBand : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBandMeanTunedTraceLane
      M m R (E : ℝ)
  let collarDeep : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarDeepTailTraceLane
      M m R (E : ℝ)
  let collarAfter : Cutoff.CutoffSample d → ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarAfterBandTraceLane
      M m R (E : ℝ)
  have hcollarBase :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.isBigOWith_upperProfileTarget_probeSharpFramedCollarBaseTraceLane_tuned
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hcollarBaseOutput
  have hcollarHead :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.collar_head_tuned_trace_is_big_o_with_eighth_power
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hcollarHeadOutput
  rcases hcollarHead with
    ⟨hcollarHeadNonneg, hcollarHeadMeasurable,
      hcollarHeadENNRealEq, hcollarHead⟩
  have hcollarBand :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.isBigOWith_upperProfileTarget_probeSharpFramedCollarBandMeanTunedTraceLane_frozenReserve
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2
        (max_le hprofileAuxLane hcollarBandOutput)
  have hcollarDeep :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.collarDeepTail_trace_isBigOWith_frozenReserve
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hcollarDeepOutput
  have hcollarAfter :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.collar_afterBand_trace_isBigOWith_frozenReserve
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2
        (max_le hprofileAuxLane hcollarAfterOutput)
  rcases hcollarAfter with
    ⟨hcollarAfterNonneg, hcollarAfterMeasurable,
      hcollarAfterENNRealEq, hcollarAfter⟩
  let collarWave : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ j : Fin d, ∑' n : ℕ,
      Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
        M R.scale (E : ℝ)
        Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
          M (E : ℝ)) n (m - 1) (basisVec j)
        (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)
        (fun eta => Algsuperdiff.Section3.Provider.Multiscale.waveTailTerm
          M R.scale (E : ℝ)
          Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB R.scale
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpLayerAnchor
            R.scale
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n) eta ^ 2)
        (Algsuperdiff.Section3.Cutoff.translateCutoffSample
          (triadicCubeShift R) omega)
  have hcollarWaveRaw :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.isBigOWith_upperProfileTarget_collarWaveTailFiniteTrace
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hcollarWaveOutput
  change (∀ omega, 0 ≤ collarWave omega) ∧ Measurable collarWave ∧
    (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal (collarWave omega) =
        ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarWavePart
            M R.scale (E : ℝ)
            Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) n (m - 1) (basisVec j)
            (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)
            (fun eta => Algsuperdiff.Section3.Provider.Multiscale.waveTailTerm
              M R.scale (E : ℝ)
              Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB R.scale
              (Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpLayerAnchor
                R.scale
                Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
                (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
                  M (E : ℝ)) n) eta ^ 2)
            (Algsuperdiff.Section3.Cutoff.translateCutoffSample
              (triadicCubeShift R) omega))) ∧
    HCPolySupport.IndependentSums.IsBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3))
      collarWave
      ((3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) *
        (Real.exp (-(Clane⁻¹ * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))) ^ 8) at hcollarWaveRaw
  rcases hcollarWaveRaw with
    ⟨hcollarWaveNonneg, hcollarWaveMeasurable,
      hcollarWaveENNRealEq, hcollarWave⟩
  obtain ⟨waveBounded, waveRare, hwave⟩ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.exists_good_wave_tail_tuned_finite_trace_split
      M hR hstate hsigma0 hsigmaHalf hmaxLane hE2 hgoodWaveOutput
  rcases hwave with
    ⟨hwaveBoundedNonneg, hwaveBoundedMeasurable,
      hwaveRareNonneg, hwaveRareMeasurable, _,
      _, hwaveENNRealDom,
      hwaveBoundedO, hwaveRareO, _, hwaveScaleLe⟩
  let perCubeScale : ℝ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude
      Clane (Disorder.cstar M) M.gamma k
  let ordinaryLane : Fin 3 → Cutoff.CutoffSample d → ℝ :=
    ![headOrdinary, deepOrdinary, afterOrdinary]
  let Uone : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ i : Fin 3, ordinaryLane i omega
  have hperCubeScalePos : 0 <
      perCubeScale :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude_pos
      hlanePos (Disorder.cstar_characterization M).1
        M.shellPrefix.gamma_pos k
  have hheadOrdinaryFull :=
    hheadOrdinaryO.mono_scale hheadOrdinaryScaleLe
  have hdeepOrdinaryFull :=
    hdeepOrdinaryO.mono_scale hdeepOrdinaryScaleLe
  have hafterOrdinaryFull :=
    hafterOrdinaryO.mono_scale hafterOrdinaryScaleLe
  have hordinaryLaneNonneg : ∀ i, ∀ omega, 0 ≤ ordinaryLane i omega := by
    intro i
    fin_cases i
    · simpa [ordinaryLane] using hheadOrdinaryNonneg
    · simpa [ordinaryLane] using hdeepOrdinaryNonneg
    · simpa [ordinaryLane] using hafterOrdinaryNonneg
  have hordinaryLaneMeasurable : ∀ i, Measurable (ordinaryLane i) := by
    intro i
    fin_cases i
    · simpa [ordinaryLane] using hheadOrdinaryMeasurable
    · simpa [ordinaryLane] using hdeepOrdinaryMeasurable
    · simpa [ordinaryLane] using hafterOrdinaryMeasurable
  have hordinaryLaneO : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      HCPolySupport.IndependentSums.IsBigO
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma 1)
        (ordinaryLane i) perCubeScale := by
    intro i _
    apply (Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg
      (hordinaryLaneNonneg i)).1
    fin_cases i
    · simpa [ordinaryLane] using hheadOrdinaryFull
    · simpa [ordinaryLane] using hdeepOrdinaryFull
    · simpa [ordinaryLane] using hafterOrdinaryFull
  have hordinarySymmetric :=
    HCPolySupport.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (Finset.univ : Finset (Fin 3)) one_pos
      ⟨0, Finset.mem_univ 0⟩
      (fun _ _ => hperCubeScalePos) hordinaryLaneO
      (fun i _ => hordinaryLaneMeasurable i)
  have hUoneNonneg : ∀ omega, 0 ≤ Uone omega := by
    intro omega
    exact Finset.sum_nonneg fun i _ => hordinaryLaneNonneg i omega
  have hUoneMeasurable : Measurable Uone := by
    exact Finset.measurable_fun_sum Finset.univ fun i _ =>
      hordinaryLaneMeasurable i
  have hUoneRaw :
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma 1) Uone
        (HCPolySupport.IndependentSums.gammaTriangleConst 1 *
          ∑ _i : Fin 3, perCubeScale) := by
    apply (Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg
      hUoneNonneg).2
    simpa only [Uone] using hordinarySymmetric
  have hUoneScale :
      HCPolySupport.IndependentSums.gammaTriangleConst 1 *
          (∑ _i : Fin 3, perCubeScale) ≤
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude
          Cblock (Disorder.cstar M) M.gamma k := by
    let Z : ℝ := (Disorder.cstar M)⁻¹ *
      min 1 (M.gamma * ((k : ℝ) + 1)) *
      (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1))
    have hZ : 0 ≤ Z := by
      dsimp only [Z]
      positivity [M.shellPrefix.gamma_pos,
        (Disorder.cstar_characterization M).1]
    have hcoeff : 3 *
          HCPolySupport.IndependentSums.gammaTriangleConst 1 ≤
        12 + 12 *
          HCPolySupport.IndependentSums.gammaTriangleConst 1 := by
      have htriangle : 0 <
          HCPolySupport.IndependentSums.gammaTriangleConst 1 :=
        HCPolySupport.IndependentSums.gammaTriangleConst_pos
      linarith
    simp only
      [perCubeScale,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    calc
      _ = (3 * HCPolySupport.IndependentSums.gammaTriangleConst 1) *
            (Clane * Z) := by
          dsimp only [Z]
          ring
      _ ≤ (12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1) *
            (Clane * Z) := by
          exact mul_le_mul_of_nonneg_right hcoeff
            (mul_nonneg hlanePos.le hZ)
      _ = _ := by
          dsimp only [Cblock, Z]
          ring
  have hUone :
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma 1)
        Uone
        (Algsuperdiff.Section3.Provider.CoarseEllipticity.upperSaturatedPerCubeAmplitude
          Cblock (Disorder.cstar M) M.gamma k) := by
    exact hUoneRaw.mono_scale hUoneScale
  have hdepthFactorPos : 0 < depthFactor := by
    dsimp only [depthFactor]
    positivity
  have hdepthFactorOne : 1 ≤ depthFactor := by
    dsimp only [depthFactor]
    exact Real.one_le_rpow (by norm_num)
      (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity))
  have hlaneEpsPos : 0 < laneEps := by
    dsimp only [laneEps]
    positivity
  have hrarePerLaneScalePos : 0 < rarePerLaneScale :=
    mul_pos hdepthFactorPos (pow_pos hlaneEpsPos 8)
  have hlaneEpsEightLe : laneEps ^ 8 ≤ rarePerLaneScale := by
    dsimp only [rarePerLaneScale]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      hdepthFactorOne (pow_nonneg hlaneEpsPos.le 8)
  have hheadRareFull :=
    hheadRareO.mono_scale (hheadRareScaleLe.trans hlaneEpsEightLe)
  have hbandRareFull :=
    hbandRareO.mono_scale (hbandRareScaleLe.trans hlaneEpsEightLe)
  have hdeepRareFull :=
    hdeepRareO.mono_scale (hdeepRareScaleLe.trans hlaneEpsEightLe)
  have hafterRareFull :
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3))
        afterRare rarePerLaneScale := by
    exact hafterRareO.mono_scale (hafterRareScaleLe.trans (by
      simpa only [rarePerLaneScale, depthFactor, laneEps,
        Nat.cast_add, Nat.cast_one] using le_rfl))
  have hwaveBoundedFull :=
    hwaveBoundedO.mono_scale (hwaveScaleLe.trans hlaneEpsEightLe)
  have hwaveRareFull :=
    hwaveRareO.mono_scale (hwaveScaleLe.trans hlaneEpsEightLe)
  have hcollarBaseNonneg : ∀ omega, 0 ≤ collarBase omega := by
    intro omega
    simpa only [collarBase] using
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseTraceLane_nonneg
        hd M R (E : ℝ)
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
            M (E : ℝ)) omega
  have hcollarBaseMeasurable : Measurable collarBase := by
    simpa only [collarBase] using
      Algsuperdiff.Section3.Provider.CoarseEllipticity.measurable_probeSharpFramedCollarBaseTraceLane
        M R (E : ℝ)
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
            M (E : ℝ))
  have hcollarBandNonneg : ∀ omega, 0 ≤ collarBand omega := by
    intro omega
    simpa only [collarBand] using
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBandMeanTunedTraceLane_nonneg
        hd M m R (E : ℝ) omega
  have hcollarBandMeasurable : Measurable collarBand := by
    simpa only [collarBand] using
      Algsuperdiff.Section3.Provider.CoarseEllipticity.measurable_probeSharpFramedCollarBandMeanTunedTraceLane
        M m R (E : ℝ)
  have hcollarDeepNonneg : ∀ omega, 0 ≤ collarDeep omega := by
    intro omega
    simpa only [collarDeep] using
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarDeepTailTraceLane_nonneg
        M m R (E : ℝ) omega
  have hcollarDeepMeasurable : Measurable collarDeep := by
    simpa only [collarDeep] using
      Algsuperdiff.Section3.Provider.CoarseEllipticity.measurable_probeSharpFramedCollarDeepTailTraceLane
        M m R (E : ℝ)
  let rareLane : Fin 12 → Cutoff.CutoffSample d → ℝ :=
    ![headRare, bandRare, deepRare, afterRare, waveBounded, waveRare,
      collarBase, collarHead, collarBand, collarDeep, collarAfter, collarWave]
  let Uexp : Cutoff.CutoffSample d → ℝ := fun omega =>
    ∑ i : Fin 12, rareLane i omega
  have hrareLaneNonneg : ∀ i, ∀ omega, 0 ≤ rareLane i omega := by
    intro i
    fin_cases i
    · simpa [rareLane] using hheadRareNonneg
    · simpa [rareLane] using hbandRareNonneg
    · simpa [rareLane] using hdeepRareNonneg
    · simpa [rareLane] using hafterRareNonneg
    · simpa [rareLane] using hwaveBoundedNonneg
    · simpa [rareLane] using hwaveRareNonneg
    · simpa [rareLane] using hcollarBaseNonneg
    · simpa [rareLane] using hcollarHeadNonneg
    · simpa [rareLane] using hcollarBandNonneg
    · simpa [rareLane] using hcollarDeepNonneg
    · simpa [rareLane] using hcollarAfterNonneg
    · simpa [rareLane] using hcollarWaveNonneg
  have hrareLaneMeasurable : ∀ i, Measurable (rareLane i) := by
    intro i
    fin_cases i
    · simpa [rareLane] using hheadRareMeasurable
    · simpa [rareLane] using hbandRareMeasurable
    · simpa [rareLane] using hdeepRareMeasurable
    · simpa [rareLane] using hafterRareMeasurable
    · simpa [rareLane] using hwaveBoundedMeasurable
    · simpa [rareLane] using hwaveRareMeasurable
    · simpa [rareLane] using hcollarBaseMeasurable
    · simpa [rareLane] using hcollarHeadMeasurable
    · simpa [rareLane] using hcollarBandMeasurable
    · simpa [rareLane] using hcollarDeepMeasurable
    · simpa [rareLane] using hcollarAfterMeasurable
    · simpa [rareLane] using hcollarWaveMeasurable
  have hrareLaneWith : ∀ i,
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3))
        (rareLane i) rarePerLaneScale := by
    intro i
    fin_cases i
    · simpa [rareLane] using hheadRareFull
    · simpa [rareLane] using hbandRareFull
    · simpa [rareLane] using hdeepRareFull
    · simpa [rareLane] using hafterRareFull
    · simpa [rareLane] using hwaveBoundedFull
    · simpa [rareLane] using hwaveRareFull
    · simpa [rareLane, rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarBase
    · simpa [rareLane, rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarHead
    · simpa [rareLane, rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarBand
    · simpa [rareLane, rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarDeep
    · simpa [rareLane, rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarAfter
    · simpa [rareLane, rarePerLaneScale, depthFactor, laneEps, laneX, inv_pow,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
        using hcollarWave
  have htargetSigmaPos : 0 < (1 - sigma) / 3 := by linarith
  have hrareLaneO : ∀ i ∈ (Finset.univ : Finset (Fin 12)),
      HCPolySupport.IndependentSums.IsBigO
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3))
        (rareLane i) rarePerLaneScale := by
    intro i _
    exact (Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg
      (hrareLaneNonneg i)).1 (hrareLaneWith i)
  have hrareSymmetric :=
    HCPolySupport.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (Finset.univ : Finset (Fin 12)) htargetSigmaPos
      ⟨0, Finset.mem_univ 0⟩
      (fun _ _ => hrarePerLaneScalePos) hrareLaneO
      (fun i _ => hrareLaneMeasurable i)
  have hUexpNonneg : ∀ omega, 0 ≤ Uexp omega := by
    intro omega
    exact Finset.sum_nonneg fun i _ => hrareLaneNonneg i omega
  have hUexpMeasurable : Measurable Uexp := by
    exact Finset.measurable_fun_sum Finset.univ fun i _ =>
      hrareLaneMeasurable i
  have hUexpRaw :
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3))
        Uexp
        (HCPolySupport.IndependentSums.gammaTriangleConst ((1 - sigma) / 3) *
          ∑ _i : Fin 12, rarePerLaneScale) := by
    apply (Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_iff_isBigO_of_nonneg
      hUexpNonneg).2
    simpa only [Uexp] using hrareSymmetric
  let K : ℝ := 12 *
    Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst
  have htriangleBarNonneg : 0 ≤
      Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst := by
    rw [Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst]
    positivity
  have hKNonneg : 0 ≤ K := by
    dsimp only [K]
    positivity
  have htriangleBound :
      HCPolySupport.IndependentSums.gammaTriangleConst ((1 - sigma) / 3) ≤
        Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst := by
    simpa only
      [Algsuperdiff.Section3.Provider.CoarseEllipticity.upperProfileTargetSigma]
      using Algsuperdiff.Section3.Provider.CoarseEllipticity.gammaTriangleConst_upperProfileTarget_le
        hsigma0 hsigmaHalf
  have hrawRareScale :
      HCPolySupport.IndependentSums.gammaTriangleConst ((1 - sigma) / 3) *
          (∑ _i : Fin 12, rarePerLaneScale) ≤
        K * rarePerLaneScale := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    calc
      HCPolySupport.IndependentSums.gammaTriangleConst ((1 - sigma) / 3) *
            (12 * rarePerLaneScale) =
          (12 * HCPolySupport.IndependentSums.gammaTriangleConst
            ((1 - sigma) / 3)) * rarePerLaneScale := by ring
      _ ≤ (12 *
            Algsuperdiff.Section3.Provider.CoarseEllipticity.upperAfterBandRareTriangleConst) *
          rarePerLaneScale :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htriangleBound (by norm_num))
          hrarePerLaneScalePos.le
      _ = K * rarePerLaneScale := by rfl
  have hUexp :
      HCPolySupport.IndependentSums.IsBigOWith
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - sigma) / 3))
        Uexp
      (K * rarePerLaneScale) := hUexpRaw.mono_scale hrawRareScale
  have hgoodBaseENNReal :
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
        (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedGoodBaseTerm
          d n (basisVec j))) =
        ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpGoodBaseConst d) := by
    change
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedGoodBaseTraceENNRealLane d = _
    exact
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedGoodBaseTraceENNRealLane_eq hd
  have hcollarBaseENNReal (omega : Cutoff.CutoffSample d) :
      (∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
        (Algsuperdiff.Section3.Provider.Multiscale.probeSharpFramedCollarBaseTerm
          M R.scale (E : ℝ)
          Algsuperdiff.Section3.Provider.CoarseEllipticity.bfaProfileB
          (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
            M (E : ℝ)) n (basisVec j)
          (Algsuperdiff.Section3.Provider.Affine.superposedGradConst d)
          (Algsuperdiff.Section3.Cutoff.translateCutoffSample
            (triadicCubeShift R) omega))) = ENNReal.ofReal (collarBase omega) := by
    change (∑ j : Fin d,
        Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseCoordinateENNRealLane
          M R (E : ℝ)
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) j omega) =
      ENNReal.ofReal
        (∑ j : Fin d,
          Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseCoordinateLane
            M R (E : ℝ)
              (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
                M (E : ℝ)) j omega)
    rw [ENNReal.ofReal_sum_of_nonneg]
    · exact Finset.sum_congr rfl fun j _ =>
        Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseCoordinateENNRealLane_eq
          hd M R (E : ℝ)
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) j omega
    · intro j _
      exact
        Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBaseCoordinateLane_nonneg
          hd M R (E : ℝ)
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.collarBandMeanDepth
              M (E : ℝ)) j omega
  have hcstarE : (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    (le_max_right _ _).trans hmaxLane
  have hcollarBandENNReal (omega : Cutoff.CutoffSample d) :
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBandMeanTunedTraceENNRealLane
          M m R (E : ℝ) omega = ENNReal.ofReal (collarBand omega) := by
    simpa only [collarBand] using
      Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBandMeanTunedTraceENNRealLane_eq
        hd M hR E.property hcstarE hE2 omega
  have hcollarDeepENNReal :
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        ENNReal.ofReal (collarDeep omega) =
          ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarDeepTailLayer
              M m R (E : ℝ) j n omega) := by
    simpa only [collarDeep] using
      Algsuperdiff.Section3.Provider.CoarseEllipticity.ae_ofReal_probeSharpFramedCollarDeepTailTraceLane_eq_sum_tsum
        M hR hstate hsigma0 hsigmaHalf hmaxLane hE2
          (max_le hprofileAuxLane hdepthThresholdLane)
  have hEnvelope (omega : Cutoff.CutoffSample d) :=
    Finset.sum_le_sum fun j (_hj : j ∈ (Finset.univ : Finset (Fin d))) =>
      ENNReal.tsum_le_tsum fun n =>
        named_layer_ennreal_bound M m (E : ℝ) R j n omega
  simp only [ENNReal.tsum_add, Finset.sum_add_distrib] at hEnvelope
  have hblockCoeff : (12 : ℝ) ≤
      12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1 :=
    le_add_of_nonneg_right (mul_nonneg (by norm_num)
      HCPolySupport.IndependentSums.gammaTriangleConst_pos.le)
  have htwoLane : Clane + Clane ≤ Cblock := by
    calc
      Clane + Clane = 2 * Clane := by ring
      _ ≤ 12 * Clane :=
        mul_le_mul_of_nonneg_right (by norm_num) hlanePos.le
      _ ≤ (12 + 12 * HCPolySupport.IndependentSums.gammaTriangleConst 1) *
          Clane := mul_le_mul_of_nonneg_right hblockCoeff hlanePos.le
      _ = Cblock := by rfl
  have hdetENNReal (omega : Cutoff.CutoffSample d) :
      ENNReal.ofReal
          (Algsuperdiff.Section3.Provider.Multiscale.probeSharpGoodBaseConst d) +
        ENNReal.ofReal (bandOrdinary omega) ≤ ENNReal.ofReal Cblock := by
    rw [← ENNReal.ofReal_add
      (Algsuperdiff.Section3.Provider.Multiscale.probeSharpGoodBaseConst_nonneg hd)
      (hbandOrdinaryNonneg omega)]
    apply ENNReal.ofReal_le_ofReal
    exact (add_le_add hgoodBaseOutput (hbandOrdinaryLe omega)).trans htwoLane
  have hCblockNonneg : 0 ≤ Cblock :=
    (add_nonneg hlanePos.le hlanePos.le).trans htwoLane
  have hcollarBandRaw (omega : Cutoff.CutoffSample d) := hcollarBandENNReal omega
  unfold
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBandMeanTunedTraceENNRealLane
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarBandMeanTunedCoordinateENNRealLane
    at hcollarBandRaw
  have hcollarDeepRaw := hcollarDeepENNReal
  unfold
    Algsuperdiff.Section3.Provider.CoarseEllipticity.probeSharpFramedCollarDeepTailLayer
    at hcollarDeepRaw
  have hUoneOfReal (omega : Cutoff.CutoffSample d) :
      ENNReal.ofReal (Uone omega) =
        ∑ i : Fin 3, ![ENNReal.ofReal (headOrdinary omega),
          ENNReal.ofReal (deepOrdinary omega), ENNReal.ofReal (afterOrdinary omega)] i := by
    change ENNReal.ofReal (∑ i : Fin 3, ordinaryLane i omega) = _
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hordinaryLaneNonneg i omega)]
    rfl
  have hUexpOfReal (omega : Cutoff.CutoffSample d) :
      ENNReal.ofReal (Uexp omega) =
        ∑ i : Fin 12, ![ENNReal.ofReal (headRare omega), ENNReal.ofReal (bandRare omega),
          ENNReal.ofReal (deepRare omega), ENNReal.ofReal (afterRare omega),
          ENNReal.ofReal (waveBounded omega), ENNReal.ofReal (waveRare omega),
          ENNReal.ofReal (collarBase omega), ENNReal.ofReal (collarHead omega),
          ENNReal.ofReal (collarBand omega), ENNReal.ofReal (collarDeep omega),
          ENNReal.ofReal (collarAfter omega), ENNReal.ofReal (collarWave omega)] i := by
    change ENNReal.ofReal (∑ i : Fin 12, rareLane i omega) = _
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hrareLaneNonneg i omega)]
    rfl
  have hae : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Algsuperdiff.Section3.Provider.CoarseEllipticity.cutoffBBlockFamily
          M m (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ R omega ≤
        Cblock + Uone omega + Uexp omega := by
    exact ae_twelve_lane_domination
      (Cutoff.cutoffSampleLaw M).toMeasure hCblockNonneg hUoneNonneg hUexpNonneg
      (hpotential k R hR) hEnvelope (fun _ => hgoodBaseENNReal)
      hheadENNRealDom hbandENNRealDom hdeepENNRealDom hafterENNRealDom hwaveENNRealDom
      hcollarBaseENNReal hcollarHeadENNRealEq hcollarBandRaw hcollarDeepRaw
      hcollarAfterENNRealEq hcollarWaveENNRealEq hdetENNReal hUoneOfReal hUexpOfReal
  have hblockMeas : Measurable (fun omega : Cutoff.CutoffSample d =>
      Algsuperdiff.Section3.Provider.CoarseEllipticity.cutoffBBlockFamily
        M m (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ R omega) := by
    have hraw : Measurable (fun omega : Cutoff.CutoffSample d =>
        HCPolySupport.Book.Ch02.matrixNorm
          (HCPolySupport.coarseBlockMatrix (cubeSet R)
            (Cutoff.coefficientCutoff M.nu m omega).toFun).upperLeft) :=
      Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseBMatrixNorm
        (Cutoff.measurable_coefficientCutoff M.nu m)
        (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m) R
    have hcoreEq :
        (fun omega : Cutoff.CutoffSample d =>
          Algsuperdiff.Section3.Provider.CoarseEllipticity.coarseBNormCoeffField R
            (Cutoff.coefficientCutoff M.nu m omega)) =
        (fun omega : Cutoff.CutoffSample d =>
          HCPolySupport.Book.Ch02.matrixNorm
            (HCPolySupport.coarseBlockMatrix (cubeSet R)
              (Cutoff.coefficientCutoff M.nu m omega).toFun).upperLeft) := by
      funext omega
      rw [Algsuperdiff.Section3.Provider.CoarseEllipticity.coarseBNormCoeffField,
        dite_eq_left (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)]
      have hbridge := congrArg
        (fun A : BlockMat d => HCPolySupport.Book.Ch02.matrixNorm A.upperLeft)
        (HCPolySupport.Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
          (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m omega) R)
      simpa only [HCPolySupport.Book.Ch02.coarseBMatrixNorm,
        HCPolySupport.Book.Ch02.coarseBlockMatrix_upperLeft] using hbridge.symm
    have hcore : Measurable (fun omega : Cutoff.CutoffSample d =>
        Algsuperdiff.Section3.Provider.CoarseEllipticity.coarseBNormCoeffField R
          (Cutoff.coefficientCutoff M.nu m omega)) := by
      rw [hcoreEq]
      exact hraw
    simpa only
      [Algsuperdiff.Section3.Provider.CoarseEllipticity.cutoffBBlockFamily] using!
        (measurable_const.mul hcore)
  simpa only [K, rarePerLaneScale, depthFactor, laneEps, laneX] using
    (nonnegative_pointwise_repair hblockMeas hUoneNonneg
      hUoneMeasurable hUexpNonneg hUexpMeasurable hUone hUexp hae)


end Algsuperdiff.Section3.Provider.CoarseEllipticity
