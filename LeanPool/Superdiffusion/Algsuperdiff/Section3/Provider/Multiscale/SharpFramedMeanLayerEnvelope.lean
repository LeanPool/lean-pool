/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedMeanLayers
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpMeanLayerEnvelope

/-!
# SharpFramedMeanLayerEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Sharp Whitney-layer envelope with the global frame retained

The framed simplex-mean wave contribution is bounded by multiplying the
existing five-term sharp wave envelope by the observation-to-cube frame.  The
frame multiplies only the wave contribution, never the complete affine layer
envelope.

These are internal conditional proof obligations.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.CoarseEllipticity

noncomputable section

variable {d : ℕ}

/-- The generic layer frame specialized to the random Whitney scale. -/
def probeSharpLayerFrame (M : ABKModel d) (m : ℤ) (E b : ℝ)
    (k₀ n : ℕ) (i : ℤ) (omega : CutoffSample d) : ℝ :=
  probeMeanLayerFrame M m (whitneyScale M m E b k₀ omega) n i

/-- The five-term sharp wave envelope with the specialized layer frame. -/
def probeSharpFramedLayerWaveEnvelope (M : ABKModel d) (m : ℤ)
    (E b : ℝ) (k₀ n : ℕ) (i L : ℤ) (omega : CutoffSample d) : ℝ :=
  probeSharpLayerFrame M m E b k₀ n i omega *
    probeSharpLayerWaveEnvelope M m E b k₀ n L omega

/-- The good/collar affine layer envelope with only its wave argument
replaced by the framed sharp wave envelope. -/
def probeSharpFramedMeanLayerEnvelope (M : ABKModel d) (m : ℤ)
    (E b : ℝ) (k₀ n : ℕ) (i L : ℤ) (omega : CutoffSample d)
    (p : Vec d) (Cgrad : ℝ) : ℝ :=
  let B := probeMeanGoodBaseConst d * vecNormSq p
  let C := probeMeanGoodWaveConst M * vecNormSq p
  let mass := probeSharpLayerMassEnvelope d n
  let collarMass := assemblyBad M E (hsep M m E b omega) k₀ n
  let wave := probeSharpFramedLayerWaveEnvelope M m E b k₀ n i L omega
  probeSharpMeanAffine B C mass wave +
    (4 * (Cgrad ^ 2 *
      (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
        (whitneyScale M m E b k₀ omega n : ℝ)))))) *
      probeSharpMeanAffine B C collarMass wave

theorem probeSharpLayerFrame_nonneg
    (M : ABKModel d) (m : ℤ) (E b : ℝ) (k₀ n : ℕ) (i : ℤ)
    (omega : CutoffSample d) :
    0 ≤ probeSharpLayerFrame M m E b k₀ n i omega := by
  exact probeMeanLayerFrame_nonneg M m
    (whitneyScale M m E b k₀ omega) n i


/-- The specialized framed fourth-mass wave factor is bounded by the framed
five-term sharp wave envelope. -/
theorem probeFramedLayerWaveFactor_le_sharpFramedLayerWaveEnvelope
    (M : ABKModel d) {m : ℤ} {E b : ℝ}
    (hb₀ : 0 < b) (hb₁ : b ≤ 1 / 8) {k₀ : ℕ} (hk₀ : 2 ≤ k₀)
    (i : ℤ) {L : ℤ} (hmL : m ≤ L) (n : ℕ)
    (omega : CutoffSample d) :
    probeFramedLayerWaveFactor M m
        (whitneyScale M m E b k₀ omega) n i L omega ≤
      probeSharpFramedLayerWaveEnvelope M m E b k₀ n i L omega := by
  have hraw := probeLayerWaveFactor_actual_le_five_sharp_terms_probe
    M (E := E) hb₀ hb₁ hk₀ hmL n omega
  have hframe := probeSharpLayerFrame_nonneg M m E b k₀ n i omega
  have hmul := mul_le_mul_of_nonneg_left hraw hframe
  simpa only [probeFramedLayerWaveFactor, probeSharpLayerFrame,
    probeSharpFramedLayerWaveEnvelope, probeMeanLayerFrame,
    probeLayerWaveFactor] using! hmul

theorem probe_framedGood_add_collar_layer_rhs_le_sharpEnvelope
    (M : ABKModel d) {m : ℤ} {E b : ℝ}
    (hd : 2 ≤ d) (hb₀ : 0 < b) (hb₁ : b ≤ 1 / 8)
    {k₀ : ℕ} (hk₀ : 2 ≤ k₀) (i : ℤ) {L : ℤ} (hmL : m ≤ L)
    (n : ℕ) (omega : CutoffSample d)
    (hne : (hsepSet M m E b omega).Nonempty)
    (p : Vec d) (Cgrad : ℝ) :
    probeFramedGoodLayerMeanRhs M m
          (whitneyScale M m E b k₀ omega) n i L omega p +
        probeFramedCollarLayerMeanRhs M m
          (whitneyScale M m E b k₀ omega) n i L omega p Cgrad b ≤
      probeSharpFramedMeanLayerEnvelope M m E b k₀ n i L omega p Cgrad := by
  let B : ℝ := probeMeanGoodBaseConst d * vecNormSq p
  let C : ℝ := probeMeanGoodWaveConst M * vecNormSq p
  let mass : ℝ := ∑ Q ∈ whitneyLayer (d := d) m
      (whitneyScale M m E b k₀ omega) n, cubeMassRatio (originCube d m) Q
  let collarMass : ℝ := ∑ Q ∈ collarLayer M m
      (whitneyScale M m E b k₀ omega) n omega,
        cubeMassRatio (originCube d m) Q
  let mass' : ℝ := probeSharpLayerMassEnvelope d n
  let collarMass' : ℝ := assemblyBad M E (hsep M m E b omega) k₀ n
  let wave : ℝ := probeFramedLayerWaveFactor M m
    (whitneyScale M m E b k₀ omega) n i L omega
  let wave' : ℝ :=
    probeSharpFramedLayerWaveEnvelope M m E b k₀ n i L omega
  have hB : 0 ≤ B :=
    mul_nonneg (probeMeanGoodBaseConst_nonneg hd) (vecNormSq_nonneg p)
  have hC : 0 ≤ C :=
    mul_nonneg (probeMeanGoodWaveConst_nonneg hd M) (vecNormSq_nonneg p)
  have hmass : 0 ≤ mass :=
    Finset.sum_nonneg fun Q _ => cubeMassRatio_nonneg _ Q
  have hcollarMass : 0 ≤ collarMass :=
    Finset.sum_nonneg fun Q _ => cubeMassRatio_nonneg _ Q
  have hmass' : 0 ≤ mass' := by
    dsimp only [mass', probeSharpLayerMassEnvelope]
    positivity
  have hcollarMass' : 0 ≤ collarMass' := by
    dsimp only [collarMass']
    exact assemblyBad_nonneg M E (hsep M m E b omega) k₀ n
  have hwave : 0 ≤ wave :=
    probeFramedLayerWaveFactor_nonneg M m
      (whitneyScale M m E b k₀ omega) n i L omega
  have hmass_le : mass ≤ mass' :=
    sum_cubeMassRatio_whitneyLayer_le m
      (whitneyScale M m E b k₀ omega) n
  have hcollarMass_le : collarMass ≤ collarMass' :=
    sum_cubeMassRatio_collarLayer_le_assemblyBad hb₀ hb₁ (by omega) hne n
  have hwave_le : wave ≤ wave' :=
    probeFramedLayerWaveFactor_le_sharpFramedLayerWaveEnvelope
      M hb₀ hb₁ hk₀ i hmL n omega
  have hgood := probeSharpMeanAffine_mono hB hC hwave hmass_le hwave_le
  have hcollar :=
    probeSharpMeanAffine_mono hB hC hwave hcollarMass_le hwave_le
  have houter : 0 ≤ 4 * (Cgrad ^ 2 *
      (3 : ℝ) ^ (2 * (b * ((n : ℝ) +
        (whitneyScale M m E b k₀ omega n : ℝ))))) := by
    positivity
  dsimp only [probeFramedGoodLayerMeanRhs, probeFramedCollarLayerMeanRhs,
    probeSharpFramedMeanLayerEnvelope, B, C, mass, collarMass, mass',
    collarMass', wave, wave'] at hgood hcollar ⊢
  exact add_le_add hgood (mul_le_mul_of_nonneg_left hcollar houter)

end

end Algsuperdiff.Section3.Provider.Multiscale
