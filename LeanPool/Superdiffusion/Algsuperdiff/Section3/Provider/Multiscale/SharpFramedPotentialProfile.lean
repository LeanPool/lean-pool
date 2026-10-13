/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileConstants
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedPotentialDescendant

/-!
# SharpFramedPotentialProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Framed sharp upper-potential bounds from the profile gate

These declarations discharge the raw bad-event gates of the framed potential
producers from the profile maximum and fifth-root hypotheses.  In particular,
none of these declarations certifies any source step or any fraction of one.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Affine
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}


/-- At a fixed strict descendant, the translated framed sharp envelope follows from
the profile gates. -/
theorem ofReal_cutoffBBlockFamily_descendant_le_sharpFramedMeanEnvelope_ae_of_profileAuxiliaryMaxGate
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {L : ℤ} (hL : m - 1 ≤ L) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal
          (cutoffBBlockFamily M L (Annealed.sigmaBar M (m - 1) : ℝ)⁻¹
            R omega) ≤
        ∑ j : Fin d, ∑' n : ℕ, ENNReal.ofReal
          (probeSharpFramedMeanLayerEnvelope M R.scale (E : ℝ) bfaProfileB k₀ n
            (m - 1) L (translateCutoffSample (triadicCubeShift R) omega)
            (basisVec j) (superposedGradConst d)) := by
  have hexp : Real.exp (profileAuxiliaryConst d / sigma) ≤ (E : ℝ) :=
    (le_max_left _ _).trans hmax
  have hEexp : Real.exp
      (badClustersConst d / bfaProfileSigma sigma) ≤ (E : ℝ) :=
    exp_badClustersConst_div_bfaProfileSigma_le_of_profileAuxiliaryGate
      hsigma0 hexp
  have hEb : badClustersConst d / bfaProfileB ≤ (E : ℝ) :=
    badClustersConst_div_bfaProfileB_le_of_profileAuxiliaryGate
      hsigma0 hsigma hexp
  obtain ⟨hE4, hunit, hgamma20, hinvSq, hgammaZ⟩ :=
    badEventGates_of_profileAuxiliaryMaxGate M E.property hsigma0 hsigma
      hmax hEgamma
  exact
    probe_ofReal_cutoffBBlockFamily_descendant_le_sharpFramedMeanEnvelope_ae
      M hR hS M.shellPrefix.dimension (bfaProfileSigma_pos hsigma0)
      (bfaProfileSigma_le_one_half hsigma) bfaProfileB_pos
      bfaProfileB_le_one_eighth hEexp hE4 hunit hgamma20 hinvSq hEb hgammaZ
      hk₀ hL


end

end Algsuperdiff.Section3.Provider.Multiscale
