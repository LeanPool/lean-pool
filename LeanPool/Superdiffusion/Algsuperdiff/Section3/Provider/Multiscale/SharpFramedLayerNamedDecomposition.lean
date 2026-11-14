/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedAfterBandScale

/-!
# SharpFramedLayerNamedDecomposition

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Literal named-lane decomposition of one framed sharp layer

This file expands `probeSharpFramedMeanLayerEnvelope` into twelve literal
nonnegative summands: the good-cell base term, five good-cell wave terms, the
collar base term, and five collar wave terms.  It is an algebraic inventory of
the already-defined envelope.  No estimate, probabilistic price, aggregation,
or cutoff-observable conclusion is asserted.

The equality prevents a later consumer from silently dropping a lane.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

variable {d : ℕ}

/-- The literal deterministic good-cell base term. -/
def probeSharpFramedGoodBaseTerm
    (d n : ℕ) (p : Vec d) : ℝ :=
  probeMeanGoodBaseConst d * vecNormSq p *
    probeSharpLayerMassEnvelope d n

/-- One named good-cell wave-square term, with the common frame, hsep power,
mean coefficient, and layer mass retained. -/
def probeSharpFramedGoodWavePart
    (M : ABKModel d) (root : ℤ) (E b : ℝ) (k₀ n : ℕ) (i : ℤ)
    (p : Vec d) (Z : CutoffSample d → ℝ) (omega : CutoffSample d) : ℝ :=
  probeMeanGoodWaveConst M * vecNormSq p *
    Real.sqrt (probeSharpLayerMassEnvelope d n) *
    probeSharpFramedAfterBandMultiplier M root E b k₀ n i omega *
    (5 * (d : ℝ) ^ 2 * Z omega)

/-- The literal nonnegative collar prefactor. -/
def probeSharpFramedCollarFactor
    (M : ABKModel d) (root : ℤ) (E b : ℝ) (k₀ n : ℕ)
    (Cgrad : ℝ) (omega : CutoffSample d) : ℝ :=
  4 * (Cgrad ^ 2 *
    (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
      (whitneyScale M root E b k₀ omega n : ℝ)))))

/-- The literal collar base term. -/
def probeSharpFramedCollarBaseTerm
    (M : ABKModel d) (root : ℤ) (E b : ℝ) (k₀ n : ℕ)
    (p : Vec d) (Cgrad : ℝ) (omega : CutoffSample d) : ℝ :=
  probeSharpFramedCollarFactor M root E b k₀ n Cgrad omega *
    (probeMeanGoodBaseConst d * vecNormSq p *
      assemblyBad M E (hsep M root E b omega) k₀ n)

/-- One named collar wave-square term, with the literal collar mass and common
framed multiplier retained. -/
def probeSharpFramedCollarWavePart
    (M : ABKModel d) (root : ℤ) (E b : ℝ) (k₀ n : ℕ) (i : ℤ)
    (p : Vec d) (Cgrad : ℝ) (Z : CutoffSample d → ℝ)
    (omega : CutoffSample d) : ℝ :=
  probeSharpFramedCollarFactor M root E b k₀ n Cgrad omega *
    (probeMeanGoodWaveConst M * vecNormSq p *
      Real.sqrt (assemblyBad M E (hsep M root E b omega) k₀ n) *
      probeSharpFramedAfterBandMultiplier M root E b k₀ n i omega *
      (5 * (d : ℝ) ^ 2 * Z omega))

/-- The complete twelve-lane named sum for one framed layer. -/
def probeSharpFramedLayerNamedSum
    (M : ABKModel d) (root : ℤ) (E b : ℝ) (k₀ n : ℕ)
    (i L : ℤ) (omega : CutoffSample d) (p : Vec d) (Cgrad : ℝ) : ℝ :=
  let ell := probeSharpLayerAnchor root b k₀ n
  let headSq := fun omega : CutoffSample d =>
    waveHeadTerm M root E b ell omega ^ 2
  let bandMeanSq := fun _omega : CutoffSample d =>
    waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2
  let deepTailSq := fun omega : CutoffSample d =>
    probeDeepBandGaugedTail M (originCube d root) ell k₀ k₀ omega ^ 2
  let afterBandSq := fun omega : CutoffSample d =>
    probeSharpAfterBandTerm M root ell k₀ L omega ^ 2
  let tailSq := fun omega : CutoffSample d =>
    waveTailTerm M root E b root ell omega ^ 2
  probeSharpFramedGoodBaseTerm d n p +
    probeSharpFramedGoodWavePart M root E b k₀ n i p headSq omega +
    probeSharpFramedGoodWavePart M root E b k₀ n i p bandMeanSq omega +
    probeSharpFramedGoodWavePart M root E b k₀ n i p deepTailSq omega +
    probeSharpFramedGoodWavePart M root E b k₀ n i p afterBandSq omega +
    probeSharpFramedGoodWavePart M root E b k₀ n i p tailSq omega +
    probeSharpFramedCollarBaseTerm M root E b k₀ n p Cgrad omega +
    probeSharpFramedCollarWavePart M root E b k₀ n i p Cgrad headSq omega +
    probeSharpFramedCollarWavePart M root E b k₀ n i p Cgrad bandMeanSq omega +
    probeSharpFramedCollarWavePart M root E b k₀ n i p Cgrad deepTailSq omega +
    probeSharpFramedCollarWavePart M root E b k₀ n i p Cgrad afterBandSq omega +
    probeSharpFramedCollarWavePart M root E b k₀ n i p Cgrad tailSq omega


theorem probeSharpFramedGoodWavePart_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (root : ℤ) (E b : ℝ)
    (k₀ n : ℕ) (i : ℤ) (p : Vec d) {Z : CutoffSample d → ℝ}
    (hZ : ∀ omega, 0 ≤ Z omega) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedGoodWavePart M root E b k₀ n i p Z omega := by
  rw [probeSharpFramedGoodWavePart]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (probeMeanGoodWaveConst_nonneg hd M) (vecNormSq_nonneg p))
        (Real.sqrt_nonneg _))
      (probeSharpFramedAfterBandMultiplier_nonneg M root E b k₀ n i omega))
    (mul_nonneg (by positivity) (hZ omega))

theorem probeSharpFramedCollarFactor_nonneg
    (M : ABKModel d) (root : ℤ) (E b : ℝ) (k₀ n : ℕ)
    (Cgrad : ℝ) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarFactor M root E b k₀ n Cgrad omega := by
  rw [probeSharpFramedCollarFactor]
  positivity

theorem probeSharpFramedCollarBaseTerm_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (root : ℤ) (E b : ℝ)
    (k₀ n : ℕ) (p : Vec d) (Cgrad : ℝ) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarBaseTerm M root E b k₀ n p Cgrad omega := by
  rw [probeSharpFramedCollarBaseTerm]
  exact mul_nonneg
    (probeSharpFramedCollarFactor_nonneg M root E b k₀ n Cgrad omega)
    (mul_nonneg
      (mul_nonneg (probeMeanGoodBaseConst_nonneg hd) (vecNormSq_nonneg p))
      (assemblyBad_nonneg M E (hsep M root E b omega) k₀ n))

theorem probeSharpFramedCollarWavePart_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (root : ℤ) (E b : ℝ)
    (k₀ n : ℕ) (i : ℤ) (p : Vec d) (Cgrad : ℝ)
    {Z : CutoffSample d → ℝ} (hZ : ∀ omega, 0 ≤ Z omega)
    (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarWavePart
      M root E b k₀ n i p Cgrad Z omega := by
  rw [probeSharpFramedCollarWavePart]
  exact mul_nonneg
    (probeSharpFramedCollarFactor_nonneg M root E b k₀ n Cgrad omega)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (probeMeanGoodWaveConst_nonneg hd M) (vecNormSq_nonneg p))
          (Real.sqrt_nonneg _))
        (probeSharpFramedAfterBandMultiplier_nonneg M root E b k₀ n i omega))
      (mul_nonneg (by positivity) (hZ omega)))

/-- Exact expansion of the framed sharp mean-layer envelope into the twelve
named lanes.  This is an equality of existing algebraic expressions, not an
estimate of any lane. -/
theorem probeSharpFramedMeanLayerEnvelope_eq_namedSum
    (M : ABKModel d) (root : ℤ) (E b : ℝ) (k₀ n : ℕ)
    (i L : ℤ) (omega : CutoffSample d) (p : Vec d) (Cgrad : ℝ) :
    probeSharpFramedMeanLayerEnvelope
        M root E b k₀ n i L omega p Cgrad =
      probeSharpFramedLayerNamedSum
        M root E b k₀ n i L omega p Cgrad := by
  unfold probeSharpFramedLayerNamedSum probeSharpFramedGoodBaseTerm
    probeSharpFramedGoodWavePart probeSharpFramedCollarBaseTerm
    probeSharpFramedCollarWavePart probeSharpFramedCollarFactor
  rw [probeSharpFramedMeanLayerEnvelope, probeSharpMeanAffine,
    probeSharpFramedLayerWaveEnvelope, probeSharpLayerWaveEnvelope,
    probeSharpFramedAfterBandMultiplier]
  unfold probeSharpMeanAffine
  ring

end

end Algsuperdiff.Section3.Provider.Multiscale
