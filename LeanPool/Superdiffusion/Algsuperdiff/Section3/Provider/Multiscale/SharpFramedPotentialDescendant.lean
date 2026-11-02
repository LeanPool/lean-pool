/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedPotentialRoot
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.BigLambdaSensitivity

/-!
# SharpFramedPotentialDescendant

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Framed sharp potential estimate at descendant cubes

This file transports the framed origin-cube estimate to a fixed descendant.
Its main theorem is an internal conditional proof obligation; the displayed
bad-event inequalities remain caller-supplied A inputs.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Affine

noncomputable section

variable {d : ℕ}

theorem cutoffBBlockFamily_translateCutoffSample_sharp_framed_probe [NeZero d]
    (M : ABKModel d) (L : ℤ) (scaling : ℝ) (R : TriadicCube d)
    (omega : CutoffSample d) :
    cutoffBBlockFamily M L scaling R omega =
      cutoffBBlockFamily M L scaling (originCube d R.scale)
        (translateCutoffSample (triadicCubeShift R) omega) := by
  classical
  rw [cutoffBBlockFamily, cutoffBBlockFamily,
    coarseBNormCoeffField, coarseBNormCoeffField,
    dite_eq_left (coefficientCutoff_aelocallyUniformlyElliptic M L omega),
    dite_eq_left (coefficientCutoff_aelocallyUniformlyElliptic M L
      (translateCutoffSample (triadicCubeShift R) omega)),
    Ch02.coarseBMatrixNorm_eq_ofAEEq
      (coefficientCutoff_canonicalFamily_aeeq M L omega) R,
    Ch02.coarseBMatrixNorm_eq_ofAEEq
      (coefficientCutoff_canonicalFamily_aeeq M L
        (translateCutoffSample (triadicCubeShift R) omega))
      (originCube d R.scale),
    coarseBMatrixNorm_cutoff_translateCutoffSample M L
      (triadicCubeShift R) (cubeSet_eq_translateSet_originCube_of_triadicCube R) omega]

/-- The normalized cutoff upper block at a fixed descendant cube, bounded
almost surely by the translated sharp layer envelope with the global
observation frame retained. -/
theorem probe_ofReal_cutoffBBlockFamily_descendant_le_sharpFramedMeanEnvelope_ae
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma b : ℝ}
    (hd : 2 ≤ d) (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hEexp : Real.exp (badClustersConst d / sigma) ≤ (E : ℝ))
    (hE4 : 4 ≤ (E : ℝ))
    (hunit : BadEvents.unitGate M)
    (hgamma20 : M.gamma ≤ 1 / 20)
    (hinvSq : ((E : ℝ)⁻¹) ^ 2 ≤ Disorder.cstar M)
    (hEb : badClustersConst d / b ≤ (E : ℝ))
    (hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ))
    {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {L : ℤ} (hL : m - 1 ≤ L) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal
          (cutoffBBlockFamily M L (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹
            R omega) ≤
        ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedMeanLayerEnvelope M R.scale (E : ℝ) b k₀ n
            (m - 1) L (translateCutoffSample (triadicCubeShift R) omega)
            (basisVec j) (superposedGradConst d)) := by
  let : NeZero d := ⟨by omega⟩
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hmi : R.scale - 1 ≤ m - 1 := by
    rw [hscale]
    omega
  have hmL : R.scale ≤ L := by
    rw [hscale]
    omega
  have hcentered : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal
          (cutoffBBlockFamily M L (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹
            (originCube d R.scale) omega) ≤
        ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedMeanLayerEnvelope M R.scale (E : ℝ) b k₀ n
            (m - 1) L omega (basisVec j) (superposedGradConst d)) := by
    exact
      probe_ofReal_cutoffBBlockFamily_inv_le_sum_tsum_sharpFramedMeanLayerEnvelope_ae
        M hS R.scale hd hsigma0 hsigma hb0 hb hEexp hE4 hunit hgamma20
          hinvSq hEb hgamma hk₀ hmi le_rfl hmL
  have htranslated : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal
          (cutoffBBlockFamily M L (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹
            (originCube d R.scale)
            (translateCutoffSample (triadicCubeShift R) omega)) ≤
        ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedMeanLayerEnvelope M R.scale (E : ℝ) b k₀ n
            (m - 1) L (translateCutoffSample (triadicCubeShift R) omega)
            (basisVec j) (superposedGradConst d)) := by
    refine MeasureTheory.ae_of_ae_map
      (p := fun omega =>
        ENNReal.ofReal
            (cutoffBBlockFamily M L
              (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹
              (originCube d R.scale) omega) ≤
          ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
            (probeSharpFramedMeanLayerEnvelope M R.scale (E : ℝ) b k₀ n
              (m - 1) L omega (basisVec j) (superposedGradConst d)))
      (measurable_translateCutoffSample (triadicCubeShift R)).aemeasurable ?_
    rw [map_translateCutoffSample_cutoffSampleLaw]
    exact hcentered
  filter_upwards [htranslated] with omega homega
  rw [cutoffBBlockFamily_translateCutoffSample_sharp_framed_probe M L
    (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹ R omega]
  exact homega

end

end Algsuperdiff.Section3.Provider.Multiscale
