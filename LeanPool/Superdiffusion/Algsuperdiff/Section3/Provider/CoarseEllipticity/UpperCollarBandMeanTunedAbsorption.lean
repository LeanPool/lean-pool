/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperAfterBandRareAbsorption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanTunedConsumption

/-!
# UpperCollarBandMeanTunedAbsorption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Terminal absorption for the tuned collar band-mean root and depth trace

This file folds the exact untranslated source root and every translated strict
depth into one block pole, then absorbs the deterministic tuned cap decay into
the frozen exceptional scale.  The depth coefficient is the internal choice
`siteRateBase d / 64`; its floor, Step-3 ceiling, and large-parameter threshold
are all derived from the existing final gate.

No mathematical premise is added to the caller surface.  This remains an
internal Provider theorem and makes no source-node or development-status claim.
-/


namespace Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

/-- The fourth-root form of the `k₀` density collapse.  Applying the existing
square-root collapse at slope `2 * b` gives the exact fourth root needed by the
collar band-mean interpolation. -/
theorem k0_fourthRoot_collapse {b t : ℝ}
    (hb0 : 0 ≤ b) (hb18 : 18 * b ≤ 1) (ht : 0 ≤ t) :
    (3 : ℝ) ^ (2 * b * t) *
        Real.sqrt (Real.sqrt
          (Real.exp (-t) + (3 : ℝ) ^ (-(t / 2)))) ≤
      2 * Real.exp (-(t / 72)) := by
  have hraw := k0_sqrt_collapse (b := 2 * b) (t := t)
    (mul_nonneg (by norm_num) hb0) (by nlinarith) ht
  have hsqrt := Real.sqrt_le_sqrt hraw
  have hleft :
      Real.sqrt ((3 : ℝ) ^ (2 * (2 * b) * t) *
        Real.sqrt (Real.exp (-t) + (3 : ℝ) ^ (-(t / 2)))) =
      (3 : ℝ) ^ (2 * b * t) *
        Real.sqrt (Real.sqrt
          (Real.exp (-t) + (3 : ℝ) ^ (-(t / 2)))) := by
    rw [Real.sqrt_mul (Real.rpow_nonneg (by norm_num) _), sqrt_three_rpow]
    congr 1
    ring_nf
  have hright :
      Real.sqrt (2 * Real.exp (-(t / 36))) ≤
        2 * Real.exp (-(t / 72)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), sqrt_exp]
    have hsqrt2 : Real.sqrt 2 ≤ (2 : ℝ) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg (2 : ℝ)]
    have hexp : -(t / 36) / 2 = -(t / 72) := by ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_right hsqrt2 (Real.exp_pos _).le
  rw [hleft] at hsqrt
  exact hsqrt.trans hright

end

end Algsuperdiff.Section3.Provider.Multiscale

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Affine
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

/-- The dimension-only prefactor left after normalizing both cap branches. -/
def collarBandMeanTunedCapPrefactor (d : ℕ) : ℝ :=
  2 * Real.sqrt (Real.sqrt (9 * (99 : ℝ) ^ d))

/-- The positive decay rate produced by the source-compatible depth choice. -/
def collarBandMeanTunedDecayRate (d : ℕ) : ℝ :=
  collarBandMeanDepthCoeff d / 72

theorem collarBandMeanTunedCapPrefactor_nonneg (d : ℕ) :
    0 ≤ collarBandMeanTunedCapPrefactor d := by
  rw [collarBandMeanTunedCapPrefactor]
  positivity

theorem collarBandMeanTunedDecayRate_pos (d : ℕ) :
    0 < collarBandMeanTunedDecayRate d := by
  rw [collarBandMeanTunedDecayRate]
  exact div_pos (collarBandMeanDepthCoeff_pos d) (by norm_num)

/-- The Step-3 ceiling turns the first density branch into the same normalized
`k₀` expression as the geometric branch. -/
theorem probeSharpCollarBandMeanCapQuarter_le_normalized
    (M : ABKModel d) (E : ℝ) (k₀ : ℕ)
    (hk₀ : (k₀ : ℝ) ≤
      siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)) :
    probeSharpCollarBandMeanCapQuarter M E k₀ ≤
      Real.sqrt (Real.sqrt (9 * (99 : ℝ) ^ d)) *
        Real.sqrt (Real.sqrt
          (Real.exp (-(k₀ : ℝ)) +
            (3 : ℝ) ^ (-((k₀ : ℝ) / 2)))) := by
  let P : ℝ := 9 * (99 : ℝ) ^ d
  let A : ℝ := Real.exp
    (-(siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))) +
      (3 : ℝ) ^ (-((k₀ : ℝ) / 2))
  let B : ℝ := Real.exp (-(k₀ : ℝ)) +
    (3 : ℝ) ^ (-((k₀ : ℝ) / 2))
  have hP : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    exact add_le_add (Real.exp_le_exp.mpr (neg_le_neg hk₀)) le_rfl
  have hcap : probeSharpCollarBandMeanCapEnvelope M E k₀ ≤ P * B := by
    rw [probeSharpCollarBandMeanCapEnvelope]
    exact mul_le_mul_of_nonneg_left hAB hP
  rw [probeSharpCollarBandMeanCapQuarter]
  calc
    Real.sqrt (Real.sqrt (probeSharpCollarBandMeanCapEnvelope M E k₀)) ≤
        Real.sqrt (Real.sqrt (P * B)) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hcap)
    _ = Real.sqrt (Real.sqrt P) * Real.sqrt (Real.sqrt B) := by
      rw [Real.sqrt_mul hP, Real.sqrt_mul (Real.sqrt_nonneg P)]
    _ = _ := by rfl

private theorem probeSharpCollarBandMeanCapGrowth_le_depthExp
    (M : ABKModel d) (E : ℝ) (k₀ : ℕ)
    (hk₀ : (k₀ : ℝ) ≤
      siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)) :
    probeSharpCollarBandMeanCapQuarter M E k₀ *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) ≤
      collarBandMeanTunedCapPrefactor d *
        Real.exp (-((k₀ : ℝ) / 72)) := by
  let P : ℝ := Real.sqrt (Real.sqrt (9 * (99 : ℝ) ^ d))
  let S : ℝ := Real.sqrt (Real.sqrt
    (Real.exp (-(k₀ : ℝ)) + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))))
  have hcap : probeSharpCollarBandMeanCapQuarter M E k₀ ≤ P * S := by
    simpa only [P, S] using
      probeSharpCollarBandMeanCapQuarter_le_normalized M E k₀ hk₀
  have hgrowth : 0 ≤ (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hcollapse :
      (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) * S ≤
        2 * Real.exp (-((k₀ : ℝ) / 72)) := by
    dsimp only [S]
    exact k0_fourthRoot_collapse bfaProfileB_pos.le
      (by norm_num [bfaProfileB]) (Nat.cast_nonneg k₀)
  calc
    probeSharpCollarBandMeanCapQuarter M E k₀ *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) ≤
      (P * S) * (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) :=
        mul_le_mul_of_nonneg_right hcap hgrowth
    _ = P * ((3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) * S) := by ring
    _ ≤ P * (2 * Real.exp (-((k₀ : ℝ) / 72))) :=
      mul_le_mul_of_nonneg_left hcollapse (by dsimp only [P]; positivity)
    _ = collarBandMeanTunedCapPrefactor d *
        Real.exp (-((k₀ : ℝ) / 72)) := by
      rw [collarBandMeanTunedCapPrefactor]
      dsimp only [P]
      ring

theorem collarBandMeanDepthCoeff_mul_invSq_gammaInv_le_depth
    (M : ABKModel d) (E : ℝ) :
    collarBandMeanDepthCoeff d * (E⁻¹ ^ 2 * M.gamma⁻¹) ≤
      (collarBandMeanDepth M E : ℝ) := by
  have hceil := Nat.le_ceil
    (collarBandMeanDepthCoeff d * (E ^ 2)⁻¹ * M.gamma⁻¹)
  rw [collarBandMeanDepth, waveBandDepth]
  calc
    collarBandMeanDepthCoeff d * (E⁻¹ ^ 2 * M.gamma⁻¹) =
        collarBandMeanDepthCoeff d * (E ^ 2)⁻¹ * M.gamma⁻¹ := by
      rw [inv_pow]
      ring
    _ ≤ (⌈collarBandMeanDepthCoeff d *
        (E ^ 2)⁻¹ * M.gamma⁻¹⌉₊ : ℝ) := hceil

/-- The complete tuned cap-growth factor decays at a positive
dimension-dependent rate.  The large-parameter premise is exactly the
internally defined threshold that pays the depth floor and ceiling error. -/
theorem probeSharpCollarBandMeanTunedCapGrowth_le_exp
    (M : ABKModel d) {E : ℝ} (hE : 0 < E)
    (hlarge : collarBandMeanDepthThreshold d ≤
      E⁻¹ ^ 2 * M.gamma⁻¹) :
    probeSharpCollarBandMeanCapQuarter M E (collarBandMeanDepth M E) *
        (3 : ℝ) ^ (2 * bfaProfileB *
          (collarBandMeanDepth M E : ℝ)) ≤
      collarBandMeanTunedCapPrefactor d *
        Real.exp (-(collarBandMeanTunedDecayRate d *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  let X : ℝ := E⁻¹ ^ 2 * M.gamma⁻¹
  let k₀ : ℕ := collarBandMeanDepth M E
  have hk₀ : (k₀ : ℝ) ≤ siteRateBase d / 2 * X := by
    dsimp only [k₀, X]
    exact waveBandDepth_collarBandMeanDepthCoeff_le_siteRate
      hE M.shellPrefix.gamma_pos rfl hlarge
  have hraw := probeSharpCollarBandMeanCapGrowth_le_depthExp M E k₀ (by
    simpa only [X] using hk₀)
  have hlower : collarBandMeanDepthCoeff d * X ≤ (k₀ : ℝ) := by
    dsimp only [k₀, X]
    exact collarBandMeanDepthCoeff_mul_invSq_gammaInv_le_depth M E
  have hexp : Real.exp (-((k₀ : ℝ) / 72)) ≤
      Real.exp (-(collarBandMeanTunedDecayRate d * X)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [collarBandMeanTunedDecayRate]
    nlinarith
  exact hraw.trans (mul_le_mul_of_nonneg_left hexp
    (collarBandMeanTunedCapPrefactor_nonneg d))
/-- Dimension-only cost after summing the exact tuned Whitney profile. -/
def collarBandMeanTunedLayerSumPrefactor (d : ℕ) : ℝ :=
  (probeSharpCollarBandMeanOuterConst d *
    (4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanMassQuarterConst d *
      (3 : ℝ) ^ (1 / 16 : ℝ))) *
    collarBandMeanTunedCapPrefactor d *
    (1 - whitneyDecayRatio)⁻¹

/-- Dimension-only finite-trace prefactor after pricing the exact hsep power. -/
def collarBandMeanTunedTracePrefactor (d : ℕ) : ℝ :=
  (d : ℝ) * collarBandMeanTunedLayerSumPrefactor d *
    superposedFluxHsepConst ^ (3 : ℝ)

theorem collarBandMeanTunedLayerSumPrefactor_nonneg
    (hd : 2 ≤ d) :
    0 ≤ collarBandMeanTunedLayerSumPrefactor d := by
  rw [collarBandMeanTunedLayerSumPrefactor]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (probeSharpCollarBandMeanOuterConst_nonneg hd)
        (by
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) (sq_nonneg _))
              (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
            (Real.rpow_nonneg (by norm_num) _)))
      (collarBandMeanTunedCapPrefactor_nonneg d))
    (inv_nonneg.mpr (sub_nonneg.mpr whitneyDecayRatio_lt_one.le))

theorem collarBandMeanTunedTracePrefactor_nonneg
    (hd : 2 ≤ d) :
    0 ≤ collarBandMeanTunedTracePrefactor d := by
  rw [collarBandMeanTunedTracePrefactor]
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg d)
      (collarBandMeanTunedLayerSumPrefactor_nonneg hd))
    (Real.rpow_nonneg superposedFluxHsepConst_pos.le _)

/-- The exact Whitney sum inherits the tuned exponential cap decay. -/
theorem tsum_probeSharpCollarBandMeanTunedLayerScale_le_exp
    (hd : 2 ≤ d) (M : ABKModel d) {E : ℝ} (hE : 0 < E)
    (hlarge : collarBandMeanDepthThreshold d ≤
      E⁻¹ ^ 2 * M.gamma⁻¹) :
    (∑' n : ℕ, probeSharpCollarBandMeanTunedLayerScale M E n) ≤
      collarBandMeanTunedLayerSumPrefactor d *
        Real.exp (-(collarBandMeanTunedDecayRate d *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  let C : ℝ := probeSharpCollarBandMeanOuterConst d *
    (4 * superposedGradConst d ^ 2 *
      probeSharpCollarBandMeanMassQuarterConst d *
      (3 : ℝ) ^ (1 / 16 : ℝ))
  let B : ℝ := probeSharpCollarBandMeanCapQuarter M E
      (collarBandMeanDepth M E) *
    (3 : ℝ) ^ (2 * bfaProfileB *
      (collarBandMeanDepth M E : ℝ))
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (probeSharpCollarBandMeanOuterConst_nonneg hd)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (sq_nonneg _))
          (probeSharpCollarBandMeanMassQuarterConst_nonneg d))
        (Real.rpow_nonneg (by norm_num) _))
  have hB := probeSharpCollarBandMeanTunedCapGrowth_le_exp
    M hE hlarge
  have hinv0 : 0 ≤ (1 - whitneyDecayRatio)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr whitneyDecayRatio_lt_one.le)
  have hsum :
      (∑' n : ℕ, probeSharpCollarBandMeanTunedLayerScale M E n) =
        C * B * (1 - whitneyDecayRatio)⁻¹ := by
    rw [show
      (fun n : ℕ => probeSharpCollarBandMeanTunedLayerScale M E n) =
        fun n : ℕ => (C * B) * whitneyDecayRatio ^ n by
      funext n
      rw [probeSharpCollarBandMeanTunedLayerScale]
      dsimp only [C, B]
      ring]
    rw [tsum_mul_left,
      tsum_geometric_of_norm_lt_one norm_whitneyDecayRatio_lt_one]
  rw [hsum]
  calc
    C * B * (1 - whitneyDecayRatio)⁻¹ ≤
        C * (collarBandMeanTunedCapPrefactor d *
          Real.exp (-(collarBandMeanTunedDecayRate d *
            (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
          (1 - whitneyDecayRatio)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hB hC0) hinv0
    _ = collarBandMeanTunedLayerSumPrefactor d *
        Real.exp (-(collarBandMeanTunedDecayRate d *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
      rw [collarBandMeanTunedLayerSumPrefactor]
      dsimp only [C]
      ring

/-- The exact hsep-power scale is bounded by a universal cube once the
auxiliary frozen gates imply `gamma ≤ bfaProfileB`. -/
theorem probeSharpCollarBandMeanTunedPowerScale_le_profileCube
    (M : ABKModel d) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hgammaB : M.gamma ≤ bfaProfileB) :
    probeSharpCollarBandMeanTunedPowerScale M sigma ≤
      superposedFluxHsepConst ^ (3 : ℝ) := by
  rw [probeSharpCollarBandMeanTunedPowerScale]
  exact hsepAmplitude_rpow_bfaPower_le_profile_cube
    (by rw [upperProfileSigma]; positivity)
    (by rw [upperProfileSigma]; linarith) hgammaB

/-- The exact strict-row finite trace has a dimension-only prefactor times the
tuned exponential decay. -/
theorem probeSharpCollarBandMeanTunedTraceScale_le_exp
    (hd : 2 ≤ d) (M : ABKModel d) {E sigma : ℝ}
    (hE : 0 < E) (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hgammaB : M.gamma ≤ bfaProfileB)
    (hlarge : collarBandMeanDepthThreshold d ≤
      E⁻¹ ^ 2 * M.gamma⁻¹) :
    probeSharpCollarBandMeanTunedTraceScale d M E sigma ≤
      collarBandMeanTunedTracePrefactor d *
        Real.exp (-(collarBandMeanTunedDecayRate d *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  let L : ℝ := ∑' n : ℕ,
    probeSharpCollarBandMeanTunedLayerScale M E n
  let KL : ℝ := collarBandMeanTunedLayerSumPrefactor d
  let Z : ℝ := Real.exp (-(collarBandMeanTunedDecayRate d *
    (E⁻¹ ^ 2 * M.gamma⁻¹)))
  let P : ℝ := probeSharpCollarBandMeanTunedPowerScale M sigma
  let KP : ℝ := superposedFluxHsepConst ^ (3 : ℝ)
  have hL : L ≤ KL * Z := by
    simpa only [L, KL, Z] using
      tsum_probeSharpCollarBandMeanTunedLayerScale_le_exp
        hd M hE hlarge
  have hP : P ≤ KP := by
    simpa only [P, KP] using
      probeSharpCollarBandMeanTunedPowerScale_le_profileCube
        M hsigma0 hsigma hgammaB
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact probeSharpCollarBandMeanTunedPowerScale_nonneg M sigma
  have hKLZ0 : 0 ≤ KL * Z :=
    mul_nonneg (collarBandMeanTunedLayerSumPrefactor_nonneg hd)
      (Real.exp_pos _).le
  have hLP : L * P ≤ (KL * Z) * KP :=
    mul_le_mul hL hP hP0 hKLZ0
  rw [probeSharpCollarBandMeanTunedTraceScale,
    probeSharpCollarBandMeanTunedCoordinateScale]
  change (d : ℝ) * (L * P) ≤ _
  calc
    (d : ℝ) * (L * P) ≤ (d : ℝ) * ((KL * Z) * KP) :=
      mul_le_mul_of_nonneg_left hLP (Nat.cast_nonneg d)
    _ = collarBandMeanTunedTracePrefactor d * Z := by
      rw [collarBandMeanTunedTracePrefactor]
      dsimp only [KL, KP]
      ring


private theorem one_le_gridNetConst_upperProfileTarget_collarBandMean
    (hd : 2 ≤ d) {sigma : ℝ} (hsigma0 : 0 < sigma)
    (hsigma : sigma ≤ 1 / 2) :
    1 ≤ gridNetConst d (upperProfileTargetSigma sigma) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hbase : 1 ≤ 3 * (d : ℝ) * Real.log 3 := by
    have hlog : 1 < Real.log 3 := one_lt_log_three
    nlinarith
  have htau0 : 0 < upperProfileTargetSigma sigma :=
    upperProfileTargetSigma_pos hsigma0 hsigma
  rw [gridNetConst]
  exact Real.one_le_rpow hbase (inv_nonneg.mpr htau0.le)


/-- Dimension-only prefactor in the terminal folded-pole gate. -/
def collarBandMeanTunedFrozenPrefactor (d : ℕ) : ℝ :=
  upperAfterBandRareTriangleConst ^ 2 *
    upperAfterBandRareGridNetConst d * (128 * (6 + 720)) *
      collarBandMeanTunedTracePrefactor d

/-- Dimension-only threshold paying the depth floor, ceiling error, fixed
prefactor, and reciprocal tuned decay rate. -/
def collarBandMeanTunedOutputConst (d : ℕ) : ℝ :=
  max (collarBandMeanDepthThreshold d)
    (1 + (collarBandMeanTunedFrozenPrefactor d + 8) *
      (collarBandMeanTunedDecayRate d)⁻¹)

theorem collarBandMeanTunedFrozenPrefactor_nonneg (hd : 2 ≤ d) :
    0 ≤ collarBandMeanTunedFrozenPrefactor d := by
  rw [collarBandMeanTunedFrozenPrefactor]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (pow_nonneg (by rw [upperAfterBandRareTriangleConst]; positivity) 2)
        (by rw [upperAfterBandRareGridNetConst]; positivity))
      (by norm_num))
    (collarBandMeanTunedTracePrefactor_nonneg hd)

theorem collarBandMeanTunedOutputConst_pos (hd : 2 ≤ d) :
    0 < collarBandMeanTunedOutputConst d := by
  rw [collarBandMeanTunedOutputConst]
  refine lt_of_lt_of_le ?_ (le_max_right _ _)
  have hK := collarBandMeanTunedFrozenPrefactor_nonneg hd
  have hr : 0 < (collarBandMeanTunedDecayRate d)⁻¹ :=
    inv_pos.mpr (collarBandMeanTunedDecayRate_pos d)
  positivity

theorem collarBandMeanDepthThreshold_le_outputConst (d : ℕ) :
    collarBandMeanDepthThreshold d ≤ collarBandMeanTunedOutputConst d := by
  rw [collarBandMeanTunedOutputConst]
  exact le_max_left _ _

private theorem collarBandMeanTuned_output_choice
    {Cup : ℝ}
    (hCup : collarBandMeanTunedOutputConst d ≤ Cup) :
    collarBandMeanTunedFrozenPrefactor d + 8 ≤
      collarBandMeanTunedDecayRate d * Cup := by
  have hsecond :
      1 + (collarBandMeanTunedFrozenPrefactor d + 8) *
          (collarBandMeanTunedDecayRate d)⁻¹ ≤ Cup :=
    (le_max_right _ _).trans (by
      simpa only [collarBandMeanTunedOutputConst] using hCup)
  have hr0 : 0 ≤ collarBandMeanTunedDecayRate d :=
    (collarBandMeanTunedDecayRate_pos d).le
  have hmul := mul_le_mul_of_nonneg_left hsecond hr0
  have hcancel : collarBandMeanTunedDecayRate d *
      ((collarBandMeanTunedFrozenPrefactor d + 8) *
        (collarBandMeanTunedDecayRate d)⁻¹) =
      collarBandMeanTunedFrozenPrefactor d + 8 := by
    field_simp [ne_of_gt (collarBandMeanTunedDecayRate_pos d)]
  nlinarith


/-- Direct per-descendant collar band-mean trace at the eighth-power reserve. -/
theorem isBigOWith_upperProfileTarget_probeSharpFramedCollarBandMeanTunedTraceLane_frozenReserve
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hCup : max (profileAuxiliaryConst d)
      (collarBandMeanTunedOutputConst d) ≤ Cup) :
    let eps := Real.exp (-(Cup⁻¹ * ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹)))
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpFramedCollarBandMeanTunedTraceLane M m R (E : ℝ))
      ((3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 8) := by
  dsimp only
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let X : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let eps : ℝ := Real.exp (-(Cup⁻¹ * X))
  let A : ℝ := probeSharpCollarBandMeanTunedTraceScale d M (E : ℝ) sigma
  let D : ℝ := collarBandMeanTunedTracePrefactor d
  let K : ℝ := collarBandMeanTunedFrozenPrefactor d
  let Z : ℝ := Real.exp (-(collarBandMeanTunedDecayRate d * X))
  have haux : profileAuxiliaryConst d ≤ Cup :=
    (le_max_left _ _).trans hCup
  have houtput : collarBandMeanTunedOutputConst d ≤ Cup :=
    (le_max_right _ _).trans hCup
  have hCup0 : 0 < Cup :=
    (collarBandMeanTunedOutputConst_pos hd).trans_le houtput
  have hmaxAux : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    refine max_le ?_ ((le_max_right _ _).trans hmax)
    exact (Real.exp_le_exp.mpr
      ((div_le_div_iff_of_pos_right hsigma0).2 haux)).trans
        ((le_max_left _ _).trans hmax)
  have hgamma : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    gamma_le_zpow_neg_five_of_frozenGate E.property
      M.shellPrefix.gamma_pos hEgamma
  have hX : Cup ≤ X := by
    dsimp only [X]
    exact outputConst_le_invSq_mul_gammaInv_of_gate M hCup0.le
      hsigma0 hsigma E.property ((le_max_left _ _).trans hmax) hgamma
  have hlarge : collarBandMeanDepthThreshold d ≤ X :=
    (collarBandMeanDepthThreshold_le_outputConst d).trans
      (houtput.trans hX)
  have hexpAux : Real.exp (profileAuxiliaryConst d / sigma) ≤ (E : ℝ) :=
    (le_max_left _ _).trans hmaxAux
  have hgammaB : M.gamma ≤ bfaProfileB := by
    calc
      M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) := hgamma
      _ ≤ (3 / 2 : ℝ) * bfaProfileB * sigma :=
        zpow_neg_five_le_three_halves_mul_bfaProfileB_of_profileAuxiliaryGate
          hsigma0 hexpAux
      _ ≤ (3 / 2 : ℝ) * bfaProfileB * (1 / 2) :=
        mul_le_mul_of_nonneg_left hsigma
          (mul_nonneg (by norm_num) bfaProfileB_pos.le)
      _ ≤ bfaProfileB := by nlinarith [bfaProfileB_pos]
  have hraw :=
    isBigOWith_upperProfileTarget_probeSharpFramedCollarBandMeanTunedTraceLane
      hd M hR hS hsigma0 hsigma hmaxAux hEgamma
  have hAexp : A ≤ D * Z := by
    dsimp only [A, D, Z]
    simpa only [X] using probeSharpCollarBandMeanTunedTraceScale_le_exp
      hd M (lt_of_lt_of_le zero_lt_one E.property) hsigma0 hsigma
        hgammaB (by simpa only [X] using hlarge)
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact collarBandMeanTunedTracePrefactor_nonneg hd
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact collarBandMeanTunedFrozenPrefactor_nonneg hd
  have hTbar1 : 1 ≤ upperAfterBandRareTriangleConst := by
    rw [upperAfterBandRareTriangleConst]
    have hp : (1 : ℝ) ≤ (117649 : ℝ) ^ (12 : ℝ) :=
      Real.one_le_rpow (by norm_num) (by norm_num)
    nlinarith
  have hGbar1 : 1 ≤ upperAfterBandRareGridNetConst d :=
    (one_le_gridNetConst_upperProfileTarget_collarBandMean
      hd hsigma0 hsigma).trans
        (gridNetConst_upperProfileTarget_le hd hsigma0 hsigma)
  have hTpow1 : 1 ≤ upperAfterBandRareTriangleConst ^ 2 := by
    nlinarith [sq_nonneg (upperAfterBandRareTriangleConst - 1)]
  have hTG1 : 1 ≤ upperAfterBandRareTriangleConst ^ 2 *
      upperAfterBandRareGridNetConst d := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hTpow1) (sub_nonneg.mpr hGbar1)]
  have hcoeff : 1 ≤ upperAfterBandRareTriangleConst ^ 2 *
      upperAfterBandRareGridNetConst d * (128 * (6 + 720) : ℝ) := by
    have hN : (1 : ℝ) ≤ 128 * (6 + 720) := by norm_num
    exact hTG1.trans (le_mul_of_one_le_right
      (zero_le_one.trans hTG1) hN)
  have hDK : D ≤ K := by
    dsimp only [D, K]
    rw [collarBandMeanTunedFrozenPrefactor]
    calc
      collarBandMeanTunedTracePrefactor d =
          1 * collarBandMeanTunedTracePrefactor d := by ring
      _ ≤ (upperAfterBandRareTriangleConst ^ 2 *
          upperAfterBandRareGridNetConst d * (128 * (6 + 720))) *
            collarBandMeanTunedTracePrefactor d :=
        mul_le_mul_of_nonneg_right hcoeff
          (collarBandMeanTunedTracePrefactor_nonneg hd)
      _ = _ := by ring
  have hZ0 : 0 ≤ Z := by dsimp only [Z]; positivity
  have hDZ : D * Z ≤ K * Z := mul_le_mul_of_nonneg_right hDK hZ0
  have hchoice := collarBandMeanTuned_output_choice houtput
  have hpref : K * Z ≤ eps ^ 8 := by
    dsimp only [K, Z, eps, X]
    exact prefactor_mul_exp_le_frozenRare_pow hK0 hCup0 hX hchoice
  have hdepth : 1 ≤ (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity))
  have hepsPow0 : 0 ≤ eps ^ 8 := pow_nonneg (Real.exp_pos _).le 8
  have htarget : eps ^ 8 ≤
      (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 8 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hdepth hepsPow0
  exact hraw.mono_scale (by
    simpa only [A, eps, X] using
      hAexp.trans (hDZ.trans (hpref.trans htarget)))

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
