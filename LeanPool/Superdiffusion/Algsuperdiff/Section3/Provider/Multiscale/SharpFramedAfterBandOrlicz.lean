/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperProfileProducts
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.HsepReduction
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedAfterBandLayerProfile

/-!
# SharpFramedAfterBandOrlicz

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Orlicz split for the actual framed after-band square

This file applies the upper-profile separation split to the literal
after-band-square summand in one sharp Whitney layer.  It treats only the
normalized inner good-mass branch, before multiplication by
`probeMeanGoodWaveConst M * vecNormSq p`.  The collar contribution, wave head,
band mean, deep-band tail, and wave tail are all excluded.  The explicit rare
scale is retained without a uniform exponential weakening.

The final two lane facts use the bounded product A directly at the explicit
witnesses `ordinaryLane = 2 * X` and `rareLane = R * X`; no choice witness is
introduced.

The declarations below are internal Provider helpers.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## Literal carriers -/

/-- The deterministic depth removed from the descendant frame. -/
def probeSharpAfterBandDescendantOffset
    (M : ABKModel d) (E : ℝ) (k n : ℕ) : ℝ :=
  (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ) +
    (waveBandDepth 1 E M.gamma : ℝ)

/-- The coefficient of the normalized good-mass after-band square before the
random frame is applied. -/
def probeSharpAfterBandGoodMassCoeff (d n : ℕ) : ℝ :=
  5 * (d : ℝ) ^ 2 * Real.sqrt (probeSharpLayerMassEnvelope d n)

/-- The `3^{gamma hsep}` factor singled out for the split. -/
def probeSharpAfterBandHsepFactor
    (M : ABKModel d) (root : ℤ) (E : ℝ)
    (omega : CutoffSample d) : ℝ :=
  (3 : ℝ) ^
    (M.gamma * (hsep M root E bfaProfileB omega : ℝ))

/-- The truncated random residual in the split. -/
def probeSharpAfterBandHsepResidual
    (M : ABKModel d) (root : ℤ) (E : ℝ)
    (omega : CutoffSample d) : ℝ :=
  probeSharpAfterBandHsepFactor M root E omega *
    (if (81 : ℝ)⁻¹ <
        M.gamma * (hsep M root E bfaProfileB omega : ℝ)
      then (1 : ℝ) else 0)


/-- The exact `Gamma_1` scale of the unframed factor. -/
def probeSharpAfterBandBaseGoodMassScale
    (M : ABKModel d) (root m : ℤ) (E : ℝ) (k n : ℕ) : ℝ :=
  let k₀ := waveBandDepth 1 E M.gamma
  let ell := probeSharpLayerAnchor root bfaProfileB k₀ n
  probeSharpAfterBandGoodMassCoeff d n *
      (3 : ℝ) ^ (-(M.gamma *
        probeSharpAfterBandDescendantOffset M E k n)) *
    probeSharpAfterBandExactScale M ell k₀ m ^ 2


/-- Exact rare-lane scale.  In particular the full hsep residual amplitude is
visible and has not been replaced by a uniform exponential envelope. -/
def probeSharpAfterBandRareGoodMassScale
    (M : ABKModel d) (root m : ℤ) (E sigma : ℝ) (k n : ℕ) : ℝ :=
  HCPolySupport.Book.Ch04.gammaProductConst
      (upperProfileHsepTau sigma) 1 *
    (HCPolySupport.Book.Ch04.gammaProductConst
          (upperProfileBaseSigma sigma) (upperProfileHsepAuxSigma sigma) *
        hsepAmplitude (upperProfileSigma sigma) bfaProfileB *
        truncationIndicatorScale bfaProfileB (upperProfileSigma sigma)
          (upperProfileHsepAuxSigma sigma)
          (hsepAmplitude (upperProfileSigma sigma) bfaProfileB)
          ⌊(81 * M.gamma)⁻¹⌋₊) *
    probeSharpAfterBandBaseGoodMassScale M root m E k n

theorem probeSharpAfterBandGoodMassCoeff_nonneg (d n : ℕ) :
    0 ≤ probeSharpAfterBandGoodMassCoeff d n := by
  rw [probeSharpAfterBandGoodMassCoeff]
  positivity

theorem probeSharpAfterBandHsepResidual_nonneg
    (M : ABKModel d) (root : ℤ) (E : ℝ) (omega : CutoffSample d) :
    0 ≤ probeSharpAfterBandHsepResidual M root E omega := by
  rw [probeSharpAfterBandHsepResidual, probeSharpAfterBandHsepFactor]
  refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
  split <;> norm_num

theorem measurable_probeSharpAfterBandHsepResidual
    (M : ABKModel d) (root : ℤ) (E : ℝ) :
    Measurable (probeSharpAfterBandHsepResidual M root E) := by
  exact measurable_comp_hsep M root E bfaProfileB fun h : ℕ =>
    (3 : ℝ) ^ (M.gamma * (h : ℝ)) *
      (if (81 : ℝ)⁻¹ < M.gamma * (h : ℝ) then (1 : ℝ) else 0)


theorem probeSharpAfterBandBaseGoodMassScale_nonneg
    (M : ABKModel d) (root m : ℤ) (E : ℝ) (k n : ℕ) :
    0 ≤ probeSharpAfterBandBaseGoodMassScale M root m E k n := by
  rw [probeSharpAfterBandBaseGoodMassScale]
  exact mul_nonneg
    (mul_nonneg (probeSharpAfterBandGoodMassCoeff_nonneg d n)
      (Real.rpow_nonneg (by norm_num) _))
    (sq_nonneg _)


/-! ## Descendant identities and the exact `Gamma_1` input -/


/-- Exact descendant normalization of the unframed `Gamma_1` scale. -/
theorem probeSharpAfterBandBaseGoodMassScale_eq_profileHalf
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) :
    probeSharpAfterBandBaseGoodMassScale M R.scale m E k n =
      5 * (d : ℝ) ^ 2 * waveSharpUpperConst d ^ 2 *
        Real.sqrt (probeSharpLayerMassEnvelope d n) *
        min 1 (M.gamma *
          (1 + (k : ℝ) + (n : ℝ) + (bfaAfterBandLayerCeil n : ℝ))) *
        (3 : ℝ) ^ (M.gamma *
          (2 + (k : ℝ) + (n : ℝ) +
            (bfaAfterBandLayerCeil n : ℝ) +
            (waveBandDepth 1 E M.gamma : ℝ))) := by
  let k₀ := waveBandDepth 1 E M.gamma
  let ell := probeSharpLayerAnchor R.scale bfaProfileB k₀ n
  let a := bfaAfterBandLayerCeil n
  let D := probeSharpAfterBandDescendantOffset M E k n
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hL : ell + (k₀ : ℤ) < m := by
    dsimp only [ell]
    rw [probeSharpLayerAnchor, hscale]
    omega
  have hgap :
      (m : ℝ) - (((ell + (k₀ : ℤ) : ℤ) : ℝ)) =
        1 + (k : ℝ) + (n : ℝ) + (a : ℝ) := by
    dsimp only [ell, a, bfaAfterBandLayerCeil]
    rw [probeSharpLayerAnchor, hscale]
    push_cast
    ring
  have hheight :
      (m : ℝ) - (ell : ℝ) =
        1 + (k : ℝ) + (n : ℝ) + (a : ℝ) + (k₀ : ℝ) := by
    dsimp only [ell, a, bfaAfterBandLayerCeil]
    rw [probeSharpLayerAnchor, hscale]
    push_cast
    ring
  have hD : D =
      (k : ℝ) + (n : ℝ) + (a : ℝ) + (k₀ : ℝ) := by
    rfl
  have hpow :
      (3 : ℝ) ^ (-(M.gamma * D)) *
          (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (ell : ℝ))) =
        (3 : ℝ) ^ (M.gamma *
          (2 + (k : ℝ) + (n : ℝ) + (a : ℝ) + (k₀ : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hheight, hD]
    congr 1
    ring
  rw [probeSharpAfterBandBaseGoodMassScale,
    probeSharpAfterBandExactScale_sq_eq_min M hL]
  change
    probeSharpAfterBandGoodMassCoeff d n * (3 : ℝ) ^ (-(M.gamma * D)) *
        (waveSharpUpperConst d ^ 2 *
          min 1
            (M.gamma * ((m : ℝ) - (((ell + (k₀ : ℤ) : ℤ) : ℝ)))) *
          (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (ell : ℝ)))) = _
  rw [hgap]
  calc
    probeSharpAfterBandGoodMassCoeff d n * (3 : ℝ) ^ (-(M.gamma * D)) *
          (waveSharpUpperConst d ^ 2 *
            min 1 (M.gamma *
              (1 + (k : ℝ) + (n : ℝ) + (a : ℝ))) *
            (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (ell : ℝ)))) =
        probeSharpAfterBandGoodMassCoeff d n * waveSharpUpperConst d ^ 2 *
          min 1 (M.gamma *
            (1 + (k : ℝ) + (n : ℝ) + (a : ℝ))) *
          ((3 : ℝ) ^ (-(M.gamma * D)) *
            (3 : ℝ) ^ (2 * M.gamma * ((m : ℝ) - (ell : ℝ)))) := by
      ring
    _ = probeSharpAfterBandGoodMassCoeff d n * waveSharpUpperConst d ^ 2 *
          min 1 (M.gamma *
            (1 + (k : ℝ) + (n : ℝ) + (a : ℝ))) *
          (3 : ℝ) ^ (M.gamma *
            (2 + (k : ℝ) + (n : ℝ) + (a : ℝ) + (k₀ : ℝ))) := by
      rw [hpow]
    _ = _ := by
      rw [probeSharpAfterBandGoodMassCoeff]
      dsimp only [a, k₀]
      ring

/-- The deterministic lane scale returned by the generic split is exactly the
verified ordinary layer scale. -/
theorem two_mul_probeSharpAfterBandBaseGoodMassScale_eq_ordinary
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    (E : ℝ) (n : ℕ) :
    2 * probeSharpAfterBandBaseGoodMassScale M R.scale m E k n =
      probeSharpAfterBandOrdinaryGoodMassLayer M E k n := by
  rw [probeSharpAfterBandBaseGoodMassScale_eq_profileHalf M hR]
  rw [probeSharpAfterBandOrdinaryGoodMassLayer]
  ring

private theorem inductionState_mono
    (M : ABKModel d) (E : {E : ℝ // 1 ≤ E}) {m₁ m₂ : ℤ}
    (hm : m₁ ≤ m₂)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m₂ E) :
    Algsuperdiff.Frozen.Section3.inductionState M m₁ E := by
  rw [Algsuperdiff.Frozen.Section3.inductionState] at hS ⊢
  exact ⟨fun i hi => hS.1 i (hi.trans hm),
    fun i hi => hS.2 i (hi.trans hm)⟩

/-! ## Exact upper-profile hsep input -/

/-- The frozen profile gates instantiate `HsepReduction` at the upper-profile
exponents.  The residual scale is kept in its exact closed form. -/
theorem probeSharpAfterBandHsep_split_of_profileAuxiliaryMaxGate
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ))) :
    (∀ omega : CutoffSample d,
        probeSharpAfterBandHsepFactor M R.scale (E : ℝ) omega ≤
          2 + probeSharpAfterBandHsepResidual M R.scale (E : ℝ) omega) ∧
      IsBigOWith (cutoffSampleLaw M).toMeasure
        (gammaSigma (upperProfileHsepTau sigma))
        (probeSharpAfterBandHsepResidual M R.scale (E : ℝ))
        (HCPolySupport.Book.Ch04.gammaProductConst
            (upperProfileBaseSigma sigma) (upperProfileHsepAuxSigma sigma) *
          hsepAmplitude (upperProfileSigma sigma) bfaProfileB *
          truncationIndicatorScale bfaProfileB (upperProfileSigma sigma)
            (upperProfileHsepAuxSigma sigma)
            (hsepAmplitude (upperProfileSigma sigma) bfaProfileB)
            ⌊(81 * M.gamma)⁻¹⌋₊) := by
  have hscale : R.scale = m - 1 - (k : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hroot : R.scale - 1 ≤ m - 1 := by
    rw [hscale]
    omega
  have hSroot : Algsuperdiff.Frozen.Section3.inductionState M (R.scale - 1) E :=
    inductionState_mono M E hroot hS
  have hexp : Real.exp (profileAuxiliaryConst d / sigma) ≤ (E : ℝ) :=
    (le_max_left _ _).trans hmax
  have hsigmaProfile0 : 0 < upperProfileSigma sigma := by
    rw [upperProfileSigma]
    positivity
  have hsigmaProfileHalf : upperProfileSigma sigma ≤ 1 / 2 := by
    rw [upperProfileSigma]
    linarith
  have hEexp : Real.exp
      (badClustersConst d / upperProfileSigma sigma) ≤ (E : ℝ) := by
    simpa only [upperProfileSigma, bfaProfileSigma] using
      exp_badClustersConst_div_bfaProfileSigma_le_of_profileAuxiliaryGate
        hsigma0 hexp
  have hEb : badClustersConst d / bfaProfileB ≤ (E : ℝ) :=
    badClustersConst_div_bfaProfileB_le_of_profileAuxiliaryGate
      hsigma0 hsigma hexp
  obtain ⟨hE4, hunit, hgamma20, hinvSq, hgammaZ⟩ :=
    badEventGates_of_profileAuxiliaryMaxGate M E.property hsigma0 hsigma
      hmax hEgamma
  have hgammaB : M.gamma ≤ bfaProfileB := by
    calc
      M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) := hgammaZ
      _ ≤ (3 / 2 : ℝ) * bfaProfileB * sigma :=
        zpow_neg_five_le_three_halves_mul_bfaProfileB_of_profileAuxiliaryGate
          hsigma0 hexp
      _ ≤ (3 / 2 : ℝ) * bfaProfileB * (1 / 2) :=
        mul_le_mul_of_nonneg_left hsigma
          (mul_nonneg (by norm_num) bfaProfileB_pos.le)
      _ ≤ bfaProfileB := by
        nlinarith [bfaProfileB_pos]
  have hsigmaAux : 0 < upperProfileHsepAuxSigma sigma :=
    upperProfileHsepAuxSigma_pos hsigma0 hsigma
  obtain ⟨hpoint, hresidual⟩ :=
    three_rpow_gamma_hsep_le_two_add_orlicz_of_gates
      (m := R.scale) (E := (E : ℝ))
      (sigma := upperProfileSigma sigma)
      (sigma2 := upperProfileHsepAuxSigma sigma)
      (b := bfaProfileB) (gam := M.gamma)
      M M.shellPrefix.dimension E.property hSroot
      hsigmaProfile0 hsigmaProfileHalf hsigmaAux
      bfaProfileB_pos bfaProfileB_le_one_eighth hEexp hE4 hunit
      hgamma20 hinvSq hEb hgammaZ M.shellPrefix.gamma_pos hgammaB
  have hexponent :
      (1 - upperProfileSigma sigma) * upperProfileHsepAuxSigma sigma /
          ((1 - upperProfileSigma sigma) + upperProfileHsepAuxSigma sigma) =
        upperProfileHsepTau sigma := by
    simpa only [upperProfileBaseSigma] using
      upperProfile_hsep_productSigma_eq hsigma0 hsigma
  rw [hexponent] at hresidual
  refine ⟨?_, ?_⟩
  · intro omega
    simpa only [probeSharpAfterBandHsepFactor,
      probeSharpAfterBandHsepResidual] using hpoint omega
  · simpa only [probeSharpAfterBandHsepFactor,
      probeSharpAfterBandHsepResidual, upperProfileBaseSigma] using! hresidual

/-! ## Explicit ordinary and rare lanes -/


end

end Algsuperdiff.Section3.Provider.Multiscale
