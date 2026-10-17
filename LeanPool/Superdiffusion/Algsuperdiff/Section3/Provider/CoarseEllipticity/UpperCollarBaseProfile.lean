/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanConsumption
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperCollarBandMeanDepthChoice
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerSeries

/-!
# UpperCollarBaseProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Literal collar-base profile

This file estimates the seventh summand of
`probeSharpFramedLayerNamedSum`, namely the literal collar base term.  It uses
both available bounds on `assemblyBad`: the density cap and the total Whitney
layer mass.  Their geometric-mean interpolation supplies the decay needed to
sum the collar growth.

The profile first retains `k₀` as an explicit deterministic parameter.  Its
terminal section then specializes to the common small dimension-dependent
choice `collarBandMeanDepth` and absorbs the resulting square-root cap decay
into the local eighth-power rare scale.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Affine
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-- Square root of the deterministic collar density cap. -/
def probeSharpCollarBaseCapHalf
    (M : ABKModel d) (E : ℝ) (k₀ : ℕ) : ℝ :=
  Real.sqrt (probeSharpCollarBandMeanCapEnvelope M E k₀)

/-- Square root of the dimension-only Whitney layer-mass prefactor. -/
def probeSharpCollarBaseMassHalfConst (d : ℕ) : ℝ :=
  Real.sqrt (6 * (d : ℝ))

/-- The deterministic coordinate scale in the literal collar-base layer
bound.  Its tuned-depth factor is deliberately retained. -/
def probeSharpCollarBaseLayerScale
    (M : ABKModel d) (E : ℝ) (k₀ n : ℕ) : ℝ :=
  (4 * superposedGradConst d ^ 2 * probeMeanGoodBaseConst d *
      probeSharpCollarBaseCapHalf M E k₀ *
      probeSharpCollarBaseMassHalfConst d *
      (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
      (3 : ℝ) ^ (1 / 16 : ℝ)) *
    whitneyDecayRatio ^ n

theorem probeSharpCollarBaseCapHalf_nonneg
    (M : ABKModel d) (E : ℝ) (k₀ : ℕ) :
    0 ≤ probeSharpCollarBaseCapHalf M E k₀ := by
  rw [probeSharpCollarBaseCapHalf]
  positivity

theorem probeSharpCollarBaseMassHalfConst_nonneg (d : ℕ) :
    0 ≤ probeSharpCollarBaseMassHalfConst d := by
  rw [probeSharpCollarBaseMassHalfConst]
  positivity


theorem probeSharpCollarBaseLayerScale_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (E : ℝ) (k₀ n : ℕ) :
    0 ≤ probeSharpCollarBaseLayerScale M E k₀ n := by
  rw [probeSharpCollarBaseLayerScale]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity) (probeMeanGoodBaseConst_nonneg hd))
            (probeSharpCollarBaseCapHalf_nonneg M E k₀))
          (probeSharpCollarBaseMassHalfConst_nonneg d))
        (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _))
    (pow_nonneg whitneyDecayRatio_nonneg n)


/-- Interpolation of the two literal `assemblyBad` bounds. -/
theorem assemblyBad_le_collarBase_geometricMean
    (M : ABKModel d) (E : ℝ) (hs k₀ n : ℕ) :
    assemblyBad M E hs k₀ n ≤
      Real.sqrt
        (probeSharpCollarBandMeanCapEnvelope M E k₀ *
          probeSharpLayerMassEnvelope d n) := by
  have hcap0 := probeSharpCollarBandMeanCapEnvelope_nonneg M E k₀
  have hmass0 := probeSharpLayerMassEnvelope_nonneg d n
  have hcap : assemblyBad M E hs k₀ n ≤
      probeSharpCollarBandMeanCapEnvelope M E k₀ :=
    (assemblyBad_le_cap M E hs k₀ n).trans
      (collarMassCap_le_probeSharpCollarBandMeanCapEnvelope M E hs k₀)
  have hmass : assemblyBad M E hs k₀ n ≤
      probeSharpLayerMassEnvelope d n := by
    simpa only [probeSharpLayerMassEnvelope] using
      assemblyBad_le_mass M E hs k₀ n
  exact (le_min hcap hmass).trans (min_le_sqrt_mul hcap0 hmass0)

/-- Exact square-root Whitney mass profile. -/
theorem sqrt_probeSharpLayerMassEnvelope_eq_collarBase
    (d n : ℕ) :
    Real.sqrt (probeSharpLayerMassEnvelope d n) =
      probeSharpCollarBaseMassHalfConst d *
        (3 : ℝ) ^ (-(n : ℝ) / 2) := by
  have hmass : 0 ≤ 6 * (d : ℝ) := by positivity
  rw [probeSharpLayerMassEnvelope, Real.sqrt_mul hmass,
    probeSharpCollarBaseMassHalfConst, sqrt_three_rpow]

/-- Exact factorization of the interpolated bad mass. -/
theorem collarBase_geometricMean_eq
    (M : ABKModel d) (E : ℝ) (k₀ n : ℕ) :
    Real.sqrt
        (probeSharpCollarBandMeanCapEnvelope M E k₀ *
          probeSharpLayerMassEnvelope d n) =
      probeSharpCollarBaseCapHalf M E k₀ *
        probeSharpCollarBaseMassHalfConst d *
        (3 : ℝ) ^ (-(n : ℝ) / 2) := by
  rw [Real.sqrt_mul
      (probeSharpCollarBandMeanCapEnvelope_nonneg M E k₀),
    probeSharpCollarBaseCapHalf,
    sqrt_probeSharpLayerMassEnvelope_eq_collarBase]
  ring

private theorem collarBase_weighted_power_le
    {b gamma : ℝ} (hb0 : 0 ≤ b) (hb64 : b ≤ 1 / 64)
    (hgamma0 : 0 ≤ gamma) (hs k₀ n c : ℕ)
    (hc : c ≤ n) :
    (3 : ℝ) ^ (2 * b *
          ((n : ℝ) + ((c + hs + k₀ : ℕ) : ℝ))) *
        (3 : ℝ) ^ (-(n : ℝ) / 2) ≤
      (3 : ℝ) ^ (2 * b * (k₀ : ℝ)) *
        (3 : ℝ) ^ ((gamma + 2 * b) * (hs : ℝ)) *
        ((3 : ℝ) ^ (1 / 16 : ℝ) * whitneyDecayRatio ^ n) := by
  have hgap : n + c ≤ 2 * n + 1 := by omega
  have hdecay := weighted_whitney_layer_factor_le
    (b := b) (gamma := (0 : ℝ)) hb0 hb64 (by norm_num)
    (by simpa using hb0) n (n + c) hgap
  have hmass : (3 : ℝ) ^ (-(n : ℝ) / 2) ≤
      (3 : ℝ) ^ (-(n : ℝ) / 4) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hgrowth0 : 0 ≤ (3 : ℝ) ^ (2 * b * ((n + c : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmassDecay :
      (3 : ℝ) ^ (-(n : ℝ) / 2) *
          (3 : ℝ) ^ (2 * b * ((n + c : ℕ) : ℝ)) ≤
        (3 : ℝ) ^ (1 / 16 : ℝ) * whitneyDecayRatio ^ n := by
    calc
      _ ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) *
          (3 : ℝ) ^ (2 * b * ((n + c : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hmass hgrowth0
      _ ≤ _ := by simpa only [add_zero] using hdecay
  have hhsep : (3 : ℝ) ^ (2 * b * (hs : ℝ)) ≤
      (3 : ℝ) ^ ((gamma + 2 * b) * (hs : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hhs : 0 ≤ (hs : ℝ) := Nat.cast_nonneg hs
    nlinarith
  have hk0 : 0 ≤ (3 : ℝ) ^ (2 * b * (k₀ : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hhsep0 : 0 ≤ (3 : ℝ) ^ (2 * b * (hs : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have htarget0 : 0 ≤ (3 : ℝ) ^ ((gamma + 2 * b) * (hs : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsplit :
      (3 : ℝ) ^ (2 * b *
          ((n : ℝ) + ((c + hs + k₀ : ℕ) : ℝ))) =
        (3 : ℝ) ^ (2 * b * (k₀ : ℝ)) *
          (3 : ℝ) ^ (2 * b * (hs : ℝ)) *
          (3 : ℝ) ^ (2 * b * ((n + c : ℕ) : ℝ)) := by
    repeat' rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [hsplit]
  calc
    _ = (3 : ℝ) ^ (2 * b * (k₀ : ℝ)) *
        (3 : ℝ) ^ (2 * b * (hs : ℝ)) *
        ((3 : ℝ) ^ (-(n : ℝ) / 2) *
          (3 : ℝ) ^ (2 * b * ((n + c : ℕ) : ℝ))) := by ring
    _ ≤ (3 : ℝ) ^ (2 * b * (k₀ : ℝ)) *
        (3 : ℝ) ^ ((gamma + 2 * b) * (hs : ℝ)) *
        ((3 : ℝ) ^ (-(n : ℝ) / 2) *
          (3 : ℝ) ^ (2 * b * ((n + c : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hhsep hk0) (mul_nonneg
          (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by norm_num) _))
    _ ≤ _ := mul_le_mul_of_nonneg_left hmassDecay
      (mul_nonneg hk0 htarget0)

/-- The actual literal collar-base summand in one Whitney layer is bounded by
the target hsep power times a summable deterministic layer profile. -/
theorem probeSharpFramedCollarBaseTerm_basisVec_le
    (hd : 2 ≤ d) (M : ABKModel d) (root : ℤ) (E : ℝ)
    (k₀ n : ℕ) (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedCollarBaseTerm M root E bfaProfileB k₀ n
        (basisVec j) (superposedGradConst d) omega ≤
      probeSharpCollarBaseLayerScale M E k₀ n *
        slstarPowerTerm M root E bfaProfileB M.gamma omega := by
  let hs := hsep M root E bfaProfileB omega
  let c := bfaAfterBandLayerCeil n
  have hc : c ≤ n := by
    simpa only [c, bfaAfterBandLayerCeil] using bfaAfterBandLayerCeil_le n
  have hbad := assemblyBad_le_collarBase_geometricMean
    M E hs k₀ n
  rw [collarBase_geometricMean_eq] at hbad
  have hpower := collarBase_weighted_power_le
    bfaProfileB_pos.le (by norm_num [bfaProfileB])
    M.shellPrefix.gamma_pos.le hs k₀ n c hc
  have hconst0 :
      0 ≤ 4 * superposedGradConst d ^ 2 * probeMeanGoodBaseConst d *
        probeSharpCollarBaseCapHalf M E k₀ *
        probeSharpCollarBaseMassHalfConst d := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (probeMeanGoodBaseConst_nonneg hd))
        (probeSharpCollarBaseCapHalf_nonneg M E k₀))
      (probeSharpCollarBaseMassHalfConst_nonneg d)
  have hfactor0 := probeSharpFramedCollarFactor_nonneg
    M root E bfaProfileB k₀ n (superposedGradConst d) omega
  have hbase0 := probeMeanGoodBaseConst_nonneg hd
  have hreplace :
      probeSharpFramedCollarBaseTerm M root E bfaProfileB k₀ n
          (basisVec j) (superposedGradConst d) omega ≤
        probeSharpFramedCollarFactor M root E bfaProfileB k₀ n
            (superposedGradConst d) omega *
          (probeMeanGoodBaseConst d *
            (probeSharpCollarBaseCapHalf M E k₀ *
              probeSharpCollarBaseMassHalfConst d *
              (3 : ℝ) ^ (-(n : ℝ) / 2))) := by
    rw [probeSharpFramedCollarBaseTerm, vecNormSq_basisVec, mul_one]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hbad hbase0) hfactor0
  refine hreplace.trans ?_
  rw [probeSharpFramedCollarFactor, whitneyScale, whitneyScaleSeq,
    probeSharpCollarBaseLayerScale, slstarPowerTerm]
  change
    4 * (superposedGradConst d ^ 2 *
        (3 : ℝ) ^ (2 * (bfaProfileB *
          ((n : ℝ) + ((c + hs + k₀ : ℕ) : ℝ))))) *
      (probeMeanGoodBaseConst d *
        (probeSharpCollarBaseCapHalf M E k₀ *
          probeSharpCollarBaseMassHalfConst d *
          (3 : ℝ) ^ (-(n : ℝ) / 2))) ≤ _
  have hpower' :
      (3 : ℝ) ^ (2 * (bfaProfileB *
          ((n : ℝ) + ((c + hs + k₀ : ℕ) : ℝ)))) *
          (3 : ℝ) ^ (-(n : ℝ) / 2) ≤
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
          (3 : ℝ) ^ ((M.gamma + 2 * bfaProfileB) * (hs : ℝ)) *
          ((3 : ℝ) ^ (1 / 16 : ℝ) * whitneyDecayRatio ^ n) := by
    simpa only [mul_assoc] using hpower
  calc
    _ = (4 * superposedGradConst d ^ 2 * probeMeanGoodBaseConst d *
          probeSharpCollarBaseCapHalf M E k₀ *
          probeSharpCollarBaseMassHalfConst d) *
        ((3 : ℝ) ^ (2 * (bfaProfileB *
            ((n : ℝ) + ((c + hs + k₀ : ℕ) : ℝ)))) *
          (3 : ℝ) ^ (-(n : ℝ) / 2)) := by ring
    _ ≤ (4 * superposedGradConst d ^ 2 * probeMeanGoodBaseConst d *
          probeSharpCollarBaseCapHalf M E k₀ *
          probeSharpCollarBaseMassHalfConst d) *
        ((3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
          (3 : ℝ) ^ ((M.gamma + 2 * bfaProfileB) * (hs : ℝ)) *
          ((3 : ℝ) ^ (1 / 16 : ℝ) * whitneyDecayRatio ^ n)) :=
      mul_le_mul_of_nonneg_left hpower' hconst0
    _ = _ := by ring

/-! ## Whitney sum, translation, and finite-coordinate trace -/

/-- The literal collar-base coordinate lane at one translated cube. -/
def probeSharpFramedCollarBaseCoordinateLane
    (M : ABKModel d) (R : TriadicCube d) (E : ℝ) (k₀ : ℕ)
    (j : Fin d) (omega : CutoffSample d) : ℝ :=
  ∑' n : ℕ,
    probeSharpFramedCollarBaseTerm M R.scale E bfaProfileB k₀ n
      (basisVec j) (superposedGradConst d)
      (translateCutoffSample (triadicCubeShift R) omega)

/-- The same literal coordinate lane in the envelope's shape. -/
def probeSharpFramedCollarBaseCoordinateENNRealLane
    (M : ABKModel d) (R : TriadicCube d) (E : ℝ) (k₀ : ℕ)
    (j : Fin d) (omega : CutoffSample d) : ENNReal :=
  ∑' n : ℕ, ENNReal.ofReal
    (probeSharpFramedCollarBaseTerm M R.scale E bfaProfileB k₀ n
      (basisVec j) (superposedGradConst d)
      (translateCutoffSample (triadicCubeShift R) omega))

/-- Pointwise majorant after summing the deterministic Whitney profile. -/
def probeSharpCollarBaseCoordinateMajorant
    (M : ABKModel d) (R : TriadicCube d) (E : ℝ) (k₀ : ℕ)
    (omega : CutoffSample d) : ℝ :=
  (∑' n : ℕ, probeSharpCollarBaseLayerScale M E k₀ n) *
    slstarPowerTerm M R.scale E bfaProfileB M.gamma
      (translateCutoffSample (triadicCubeShift R) omega)

/-- Exact Orlicz scale of one translated coordinate lane. -/
def probeSharpCollarBaseCoordinateScale
    (M : ABKModel d) (E sigma : ℝ) (k₀ : ℕ) : ℝ :=
  (∑' n : ℕ, probeSharpCollarBaseLayerScale M E k₀ n) *
    probeSharpCollarBandMeanPowerScale M sigma

/-- The literal finite-coordinate collar-base trace. -/
def probeSharpFramedCollarBaseTraceLane
    (M : ABKModel d) (R : TriadicCube d) (E : ℝ) (k₀ : ℕ)
    (omega : CutoffSample d) : ℝ :=
  ∑ j : Fin d, probeSharpFramedCollarBaseCoordinateLane M R E k₀ j omega

/-- The exact finite-coordinate trace scale. -/
def probeSharpCollarBaseTraceScale
    (d : ℕ) (M : ABKModel d) (E sigma : ℝ) (k₀ : ℕ) : ℝ :=
  (d : ℝ) * probeSharpCollarBaseCoordinateScale M E sigma k₀

private theorem measurable_probeSharpFramedCollarBaseLayer
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k₀ n : ℕ)
    (j : Fin d) :
    Measurable fun omega : CutoffSample d =>
      probeSharpFramedCollarBaseTerm M root E bfaProfileB k₀ n
        (basisVec j) (superposedGradConst d) omega := by
  have hfactor : Measurable fun omega : CutoffSample d =>
      probeSharpFramedCollarFactor M root E bfaProfileB k₀ n
        (superposedGradConst d) omega :=
    measurable_comp_hsep M root E bfaProfileB fun hs : ℕ =>
      4 * (superposedGradConst d ^ 2 *
        (3 : ℝ) ^ (2 * (bfaProfileB * ((n : ℝ) +
          (whitneyScaleSeq bfaProfileB hs k₀ n : ℝ)))))
  have hbad : Measurable fun omega : CutoffSample d =>
      assemblyBad M E (hsep M root E bfaProfileB omega) k₀ n :=
    measurable_comp_hsep M root E bfaProfileB fun hs : ℕ =>
      assemblyBad M E hs k₀ n
  simpa only [probeSharpFramedCollarBaseTerm] using!
    hfactor.mul (measurable_const.mul hbad)

theorem summable_probeSharpCollarBaseLayerScale
    (M : ABKModel d) (E : ℝ) (k₀ : ℕ) :
    Summable fun n : ℕ => probeSharpCollarBaseLayerScale M E k₀ n := by
  have hgeom : Summable fun n : ℕ => whitneyDecayRatio ^ n :=
    summable_geometric_of_norm_lt_one norm_whitneyDecayRatio_lt_one
  exact hgeom.mul_left
    (4 * superposedGradConst d ^ 2 * probeMeanGoodBaseConst d *
      probeSharpCollarBaseCapHalf M E k₀ *
      probeSharpCollarBaseMassHalfConst d *
      (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) *
      (3 : ℝ) ^ (1 / 16 : ℝ))

theorem summable_probeSharpFramedCollarBaseCoordinateLayer
    (hd : 2 ≤ d) (M : ABKModel d) (R : TriadicCube d)
    (E : ℝ) (k₀ : ℕ) (j : Fin d) (omega : CutoffSample d) :
    Summable fun n : ℕ =>
      probeSharpFramedCollarBaseTerm M R.scale E bfaProfileB k₀ n
        (basisVec j) (superposedGradConst d)
        (translateCutoffSample (triadicCubeShift R) omega) := by
  let P := slstarPowerTerm M R.scale E bfaProfileB M.gamma
    (translateCutoffSample (triadicCubeShift R) omega)
  have hmajor : Summable fun n : ℕ =>
      probeSharpCollarBaseLayerScale M E k₀ n * P :=
    (summable_probeSharpCollarBaseLayerScale M E k₀).mul_right P
  exact Summable.of_nonneg_of_le
    (fun n => probeSharpFramedCollarBaseTerm_nonneg hd M R.scale E
      bfaProfileB k₀ n (basisVec j) (superposedGradConst d)
      (translateCutoffSample (triadicCubeShift R) omega))
    (fun n => probeSharpFramedCollarBaseTerm_basisVec_le hd M R.scale E
      k₀ n j (translateCutoffSample (triadicCubeShift R) omega))
    hmajor

theorem probeSharpFramedCollarBaseCoordinateLane_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (R : TriadicCube d)
    (E : ℝ) (k₀ : ℕ) (j : Fin d) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarBaseCoordinateLane M R E k₀ j omega := by
  rw [probeSharpFramedCollarBaseCoordinateLane]
  exact tsum_nonneg fun n =>
    probeSharpFramedCollarBaseTerm_nonneg hd M R.scale E bfaProfileB
      k₀ n (basisVec j) (superposedGradConst d)
      (translateCutoffSample (triadicCubeShift R) omega)

theorem measurable_probeSharpFramedCollarBaseCoordinateLane
    (M : ABKModel d) (R : TriadicCube d) (E : ℝ) (k₀ : ℕ)
    (j : Fin d) :
    Measurable (probeSharpFramedCollarBaseCoordinateLane M R E k₀ j) := by
  have hnn : Measurable (fun omega : CutoffSample d => ∑' n : ℕ,
      (probeSharpFramedCollarBaseTerm M R.scale E bfaProfileB k₀ n
        (basisVec j) (superposedGradConst d)
        (translateCutoffSample (triadicCubeShift R) omega)).toNNReal) :=
    Measurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      ((measurable_probeSharpFramedCollarBaseLayer M R.scale E k₀ n j).comp
        (measurable_translateCutoffSample (triadicCubeShift R))).real_toNNReal
  have hnn := hnn.coe_nnreal_real
  convert hnn using 1
  funext omega
  rw [probeSharpFramedCollarBaseCoordinateLane, NNReal.coe_tsum]
  apply tsum_congr
  intro n
  rw [Real.toNNReal_of_nonneg
    (probeSharpFramedCollarBaseTerm_nonneg M.shellPrefix.dimension M
      R.scale E bfaProfileB k₀ n (basisVec j) (superposedGradConst d)
      (translateCutoffSample (triadicCubeShift R) omega))]
  rfl

theorem probeSharpFramedCollarBaseCoordinateLane_le_majorant
    (hd : 2 ≤ d) (M : ABKModel d) (R : TriadicCube d)
    (E : ℝ) (k₀ : ℕ) (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedCollarBaseCoordinateLane M R E k₀ j omega ≤
      probeSharpCollarBaseCoordinateMajorant M R E k₀ omega := by
  let P := slstarPowerTerm M R.scale E bfaProfileB M.gamma
    (translateCutoffSample (triadicCubeShift R) omega)
  have hleft := summable_probeSharpFramedCollarBaseCoordinateLayer
    hd M R E k₀ j omega
  have hright : Summable fun n : ℕ =>
      probeSharpCollarBaseLayerScale M E k₀ n * P :=
    (summable_probeSharpCollarBaseLayerScale M E k₀).mul_right P
  rw [probeSharpFramedCollarBaseCoordinateLane,
    probeSharpCollarBaseCoordinateMajorant]
  calc
    _ ≤ ∑' n : ℕ, probeSharpCollarBaseLayerScale M E k₀ n * P :=
      Summable.tsum_le_tsum
        (fun n => probeSharpFramedCollarBaseTerm_basisVec_le hd M R.scale E
          k₀ n j (translateCutoffSample (triadicCubeShift R) omega))
        hleft hright
    _ = (∑' n : ℕ, probeSharpCollarBaseLayerScale M E k₀ n) * P := by
      rw [tsum_mul_right]

theorem probeSharpFramedCollarBaseCoordinateENNRealLane_eq
    (hd : 2 ≤ d) (M : ABKModel d) (R : TriadicCube d)
    (E : ℝ) (k₀ : ℕ) (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedCollarBaseCoordinateENNRealLane M R E k₀ j omega =
      ENNReal.ofReal
        (probeSharpFramedCollarBaseCoordinateLane M R E k₀ j omega) := by
  rw [probeSharpFramedCollarBaseCoordinateENNRealLane,
    probeSharpFramedCollarBaseCoordinateLane]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun n => probeSharpFramedCollarBaseTerm_nonneg hd M R.scale E
      bfaProfileB k₀ n (basisVec j) (superposedGradConst d)
      (translateCutoffSample (triadicCubeShift R) omega))
    (summable_probeSharpFramedCollarBaseCoordinateLayer
      hd M R E k₀ j omega)).symm


private theorem measurable_slstarPowerTerm_collarBase
    (M : ABKModel d) (root : ℤ) (E b gam : ℝ) :
    Measurable (slstarPowerTerm M root E b gam) := by
  simpa only [slstarPowerTerm] using!
    measurable_comp_hsep M root E b fun hs : ℕ =>
      (3 : ℝ) ^ ((gam + 2 * b) * (hs : ℝ))

theorem isBigOWith_upperProfileTarget_probeSharpCollarBaseCoordinateMajorant
    (hd : 2 ≤ d) (M : ABKModel d)
    {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (k₀ : ℕ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpCollarBaseCoordinateMajorant M R (E : ℝ) k₀)
      (probeSharpCollarBaseCoordinateScale M (E : ℝ) sigma k₀) := by
  have hpower := isBigOWith_upperProfileTarget_slstarPowerTerm
    M hR hS hsigma0 hsigma hmax hEgamma
  have htranslated :=
    Algsuperdiff.Section3.Provider.Stream.isBigOWith_comp_translateCutoffSample
      M (triadicCubeShift R)
      (measurable_slstarPowerTerm_collarBase
        M R.scale (E : ℝ) bfaProfileB M.gamma)
      hpower
  have hsum0 : 0 ≤
      ∑' n : ℕ, probeSharpCollarBaseLayerScale M (E : ℝ) k₀ n :=
    tsum_nonneg fun n =>
      probeSharpCollarBaseLayerScale_nonneg hd M (E : ℝ) k₀ n
  have hscaled := htranslated.const_mul hsum0
  simpa only [probeSharpCollarBaseCoordinateMajorant,
    probeSharpCollarBaseCoordinateScale] using! hscaled

/-- The actual translated literal collar-base coordinate has the target rare
exponent, with no supplied estimate premise. -/
theorem isBigOWith_upperProfileTarget_probeSharpFramedCollarBaseCoordinateLane
    (hd : 2 ≤ d) (M : ABKModel d)
    {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (k₀ : ℕ) (j : Fin d) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpFramedCollarBaseCoordinateLane M R (E : ℝ) k₀ j)
      (probeSharpCollarBaseCoordinateScale M (E : ℝ) sigma k₀) := by
  exact isBigOWith_gammaSigma_of_le
    (fun omega => probeSharpFramedCollarBaseCoordinateLane_le_majorant
      hd M R (E : ℝ) k₀ j omega)
    (isBigOWith_upperProfileTarget_probeSharpCollarBaseCoordinateMajorant
      hd M hR hS hsigma0 hsigma hmax hEgamma k₀)

theorem probeSharpFramedCollarBaseCoordinateLane_eq
    (M : ABKModel d) (R : TriadicCube d) (E : ℝ) (k₀ : ℕ)
    (j j' : Fin d) :
    probeSharpFramedCollarBaseCoordinateLane M R E k₀ j =
      probeSharpFramedCollarBaseCoordinateLane M R E k₀ j' := by
  funext omega
  rw [probeSharpFramedCollarBaseCoordinateLane,
    probeSharpFramedCollarBaseCoordinateLane]
  apply tsum_congr
  intro n
  simp only [probeSharpFramedCollarBaseTerm, vecNormSq_basisVec]

theorem probeSharpFramedCollarBaseTraceLane_eq_dimension_mul
    (M : ABKModel d) (R : TriadicCube d) (E : ℝ) (k₀ : ℕ)
    (j : Fin d) (omega : CutoffSample d) :
    probeSharpFramedCollarBaseTraceLane M R E k₀ omega =
      (d : ℝ) * probeSharpFramedCollarBaseCoordinateLane M R E k₀ j omega := by
  rw [probeSharpFramedCollarBaseTraceLane]
  have hall : ∀ j' : Fin d,
      probeSharpFramedCollarBaseCoordinateLane M R E k₀ j' omega =
        probeSharpFramedCollarBaseCoordinateLane M R E k₀ j omega :=
    fun j' => congrFun
      (probeSharpFramedCollarBaseCoordinateLane_eq M R E k₀ j' j) omega
  simp_rw [hall]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

theorem probeSharpFramedCollarBaseTraceLane_nonneg
    (hd : 2 ≤ d) (M : ABKModel d) (R : TriadicCube d)
    (E : ℝ) (k₀ : ℕ) (omega : CutoffSample d) :
    0 ≤ probeSharpFramedCollarBaseTraceLane M R E k₀ omega := by
  rw [probeSharpFramedCollarBaseTraceLane]
  exact Finset.sum_nonneg fun j _ =>
    probeSharpFramedCollarBaseCoordinateLane_nonneg
      hd M R E k₀ j omega

theorem measurable_probeSharpFramedCollarBaseTraceLane
    (M : ABKModel d) (R : TriadicCube d) (E : ℝ) (k₀ : ℕ) :
    Measurable (probeSharpFramedCollarBaseTraceLane M R E k₀) := by
  change Measurable fun omega : CutoffSample d =>
    ∑ j : Fin d,
      probeSharpFramedCollarBaseCoordinateLane M R E k₀ j omega
  exact Finset.measurable_fun_sum Finset.univ fun j _ =>
    measurable_probeSharpFramedCollarBaseCoordinateLane M R E k₀ j

theorem isBigOWith_upperProfileTarget_probeSharpFramedCollarBaseTraceLane
    (hd : 2 ≤ d) (M : ABKModel d)
    {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (profileAuxiliaryConst d / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (k₀ : ℕ) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma (upperProfileTargetSigma sigma))
      (probeSharpFramedCollarBaseTraceLane M R (E : ℝ) k₀)
      (probeSharpCollarBaseTraceScale d M (E : ℝ) sigma k₀) := by
  let j₀ : Fin d :=
    ⟨0, Nat.zero_lt_of_lt M.shellPrefix.dimension⟩
  have hcoord :=
    isBigOWith_upperProfileTarget_probeSharpFramedCollarBaseCoordinateLane
      hd M hR hS hsigma0 hsigma hmax hEgamma k₀ j₀
  have hscaled := hcoord.const_mul (Nat.cast_nonneg d)
  have hlane : probeSharpFramedCollarBaseTraceLane M R (E : ℝ) k₀ =
      fun omega => (d : ℝ) *
        probeSharpFramedCollarBaseCoordinateLane
          M R (E : ℝ) k₀ j₀ omega := by
    funext omega
    exact probeSharpFramedCollarBaseTraceLane_eq_dimension_mul
      M R (E : ℝ) k₀ j₀ omega
  rw [hlane]
  simpa only [probeSharpCollarBaseTraceScale] using hscaled

/-! ## Tuned-depth terminal estimate -/

/-- Dimension-only prefactor remaining after the tuned collar density collapse,
Whitney summation, finite-coordinate trace, and hsep-power estimate. -/
def probeSharpCollarBaseTunedTracePrefactor (d : ℕ) : ℝ :=
  (d : ℝ) *
    ((4 * superposedGradConst d ^ 2 * probeMeanGoodBaseConst d *
        probeSharpCollarBaseMassHalfConst d *
        (3 : ℝ) ^ (1 / 16 : ℝ)) *
      (2 * Real.sqrt (9 * (99 : ℝ) ^ d)) *
      (1 - whitneyDecayRatio)⁻¹) *
    superposedFluxHsepConst ^ (3 : ℝ)

/-- Dimension-only threshold which pays the profile gate, tuned-depth rounding,
the collar-base trace prefactor, and eight copies of the frozen rare scale. -/
def probeSharpCollarBaseTunedOutputConst (d : ℕ) : ℝ :=
  max (profileAuxiliaryConst d)
    (max (collarBandMeanDepthThreshold d)
      (1 + (probeSharpCollarBaseTunedTracePrefactor d + 8) *
        (collarBandMeanDepthCoeff d / 36)⁻¹))

private theorem probeSharpCollarBaseTunedTracePrefactor_nonneg
    (hd : 2 ≤ d) :
    0 ≤ probeSharpCollarBaseTunedTracePrefactor d := by
  rw [probeSharpCollarBaseTunedTracePrefactor]
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity)
                (probeMeanGoodBaseConst_nonneg hd))
              (probeSharpCollarBaseMassHalfConst_nonneg d))
            (Real.rpow_nonneg (by norm_num) _))
          (by positivity))
        (inv_nonneg.mpr
          (sub_nonneg.mpr whitneyDecayRatio_lt_one.le))))
    (Real.rpow_nonneg superposedFluxHsepConst_pos.le _)

theorem probeSharpCollarBaseTunedOutputConst_pos (d : ℕ) :
    0 < probeSharpCollarBaseTunedOutputConst d := by
  rw [probeSharpCollarBaseTunedOutputConst]
  exact (collarBandMeanDepthThreshold_pos d).trans_le
    ((le_max_left _ _).trans (le_max_right _ _))

private theorem probeSharpCollarBaseCapHalf_le_normalized
    (M : ABKModel d) (E : ℝ) (k₀ : ℕ)
    (hk₀ : (k₀ : ℝ) ≤
      siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)) :
    probeSharpCollarBaseCapHalf M E k₀ ≤
      Real.sqrt (9 * (99 : ℝ) ^ d) *
        Real.sqrt
          (Real.exp (-(k₀ : ℝ)) +
            (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) := by
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
  rw [probeSharpCollarBaseCapHalf]
  calc
    Real.sqrt (probeSharpCollarBandMeanCapEnvelope M E k₀) ≤
        Real.sqrt (P * B) := Real.sqrt_le_sqrt hcap
    _ = Real.sqrt P * Real.sqrt B := by rw [Real.sqrt_mul hP]
    _ = _ := by rfl

private theorem probeSharpCollarBaseCapGrowth_le_depthExp
    (M : ABKModel d) (E : ℝ) (k₀ : ℕ)
    (hk₀ : (k₀ : ℝ) ≤
      siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)) :
    probeSharpCollarBaseCapHalf M E k₀ *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) ≤
      (2 * Real.sqrt (9 * (99 : ℝ) ^ d)) *
        Real.exp (-((k₀ : ℝ) / 36)) := by
  let P : ℝ := Real.sqrt (9 * (99 : ℝ) ^ d)
  let S : ℝ := Real.sqrt
    (Real.exp (-(k₀ : ℝ)) + (3 : ℝ) ^ (-((k₀ : ℝ) / 2)))
  have hcap : probeSharpCollarBaseCapHalf M E k₀ ≤ P * S := by
    simpa only [P, S] using
      probeSharpCollarBaseCapHalf_le_normalized M E k₀ hk₀
  have hgrowth : 0 ≤ (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hcollapse :
      (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) * S ≤
        2 * Real.exp (-((k₀ : ℝ) / 36)) := by
    dsimp only [S]
    exact k0_sqrt_collapse bfaProfileB_pos.le
      (by norm_num [bfaProfileB]) (Nat.cast_nonneg k₀)
  calc
    probeSharpCollarBaseCapHalf M E k₀ *
        (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) ≤
      (P * S) * (3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) :=
        mul_le_mul_of_nonneg_right hcap hgrowth
    _ = P * ((3 : ℝ) ^ (2 * bfaProfileB * (k₀ : ℝ)) * S) := by
      ring
    _ ≤ P * (2 * Real.exp (-((k₀ : ℝ) / 36))) :=
      mul_le_mul_of_nonneg_left hcollapse (by dsimp only [P]; positivity)
    _ = (2 * Real.sqrt (9 * (99 : ℝ) ^ d)) *
        Real.exp (-((k₀ : ℝ) / 36)) := by
      dsimp only [P]
      ring

private theorem collarBase_depthCoeff_mul_invSq_gammaInv_le_depth
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

private theorem probeSharpCollarBaseTunedCapGrowth_le_exp
    (M : ABKModel d) {E : ℝ} (hE : 0 < E)
    (hlarge : collarBandMeanDepthThreshold d ≤
      E⁻¹ ^ 2 * M.gamma⁻¹) :
    probeSharpCollarBaseCapHalf M E (collarBandMeanDepth M E) *
        (3 : ℝ) ^ (2 * bfaProfileB *
          (collarBandMeanDepth M E : ℝ)) ≤
      (2 * Real.sqrt (9 * (99 : ℝ) ^ d)) *
        Real.exp (-((collarBandMeanDepthCoeff d / 36) *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  let X : ℝ := E⁻¹ ^ 2 * M.gamma⁻¹
  let k₀ : ℕ := collarBandMeanDepth M E
  have hk₀ : (k₀ : ℝ) ≤ siteRateBase d / 2 * X := by
    dsimp only [k₀, X]
    exact waveBandDepth_collarBandMeanDepthCoeff_le_siteRate
      hE M.shellPrefix.gamma_pos rfl hlarge
  have hraw := probeSharpCollarBaseCapGrowth_le_depthExp M E k₀ (by
    simpa only [X] using hk₀)
  have hlower : collarBandMeanDepthCoeff d * X ≤ (k₀ : ℝ) := by
    dsimp only [k₀, X]
    exact collarBase_depthCoeff_mul_invSq_gammaInv_le_depth M E
  have hexp : Real.exp (-((k₀ : ℝ) / 36)) ≤
      Real.exp (-((collarBandMeanDepthCoeff d / 36) * X)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  exact hraw.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

private theorem probeSharpCollarBasePowerScale_le_profileCube
    (M : ABKModel d) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hgammaB : M.gamma ≤ bfaProfileB) :
    probeSharpCollarBandMeanPowerScale M sigma ≤
      superposedFluxHsepConst ^ (3 : ℝ) := by
  rw [probeSharpCollarBandMeanPowerScale]
  exact hsepAmplitude_rpow_bfaPower_le_profile_cube
    (by rw [upperProfileSigma]; positivity)
    (by rw [upperProfileSigma]; linarith) hgammaB

private theorem probeSharpCollarBaseTraceScale_tuned_le_exp
    (hd : 2 ≤ d) (M : ABKModel d) {E sigma : ℝ}
    (hE : 0 < E) (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hgammaB : M.gamma ≤ bfaProfileB)
    (hlarge : collarBandMeanDepthThreshold d ≤
      E⁻¹ ^ 2 * M.gamma⁻¹) :
    probeSharpCollarBaseTraceScale d M E sigma
        (collarBandMeanDepth M E) ≤
      probeSharpCollarBaseTunedTracePrefactor d *
        Real.exp (-((collarBandMeanDepthCoeff d / 36) *
          (E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  let C : ℝ := 4 * superposedGradConst d ^ 2 *
    probeMeanGoodBaseConst d * probeSharpCollarBaseMassHalfConst d *
      (3 : ℝ) ^ (1 / 16 : ℝ)
  let B : ℝ := probeSharpCollarBaseCapHalf M E
      (collarBandMeanDepth M E) *
    (3 : ℝ) ^ (2 * bfaProfileB *
      (collarBandMeanDepth M E : ℝ))
  let D : ℝ := 2 * Real.sqrt (9 * (99 : ℝ) ^ d)
  let Z : ℝ := Real.exp (-((collarBandMeanDepthCoeff d / 36) *
    (E⁻¹ ^ 2 * M.gamma⁻¹)))
  let L : ℝ := ∑' n : ℕ,
    probeSharpCollarBaseLayerScale M E (collarBandMeanDepth M E) n
  let P : ℝ := probeSharpCollarBandMeanPowerScale M sigma
  let KP : ℝ := superposedFluxHsepConst ^ (3 : ℝ)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg (superposedGradConst d)))
          (probeMeanGoodBaseConst_nonneg hd))
        (probeSharpCollarBaseMassHalfConst_nonneg d))
      (Real.rpow_nonneg (by norm_num) _)
  have hB : B ≤ D * Z := by
    simpa only [B, D, Z] using
      probeSharpCollarBaseTunedCapGrowth_le_exp M hE hlarge
  have hinv0 : 0 ≤ (1 - whitneyDecayRatio)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr whitneyDecayRatio_lt_one.le)
  have hL : L ≤ C * (D * Z) * (1 - whitneyDecayRatio)⁻¹ := by
    have hsum : L = C * B * (1 - whitneyDecayRatio)⁻¹ := by
      dsimp only [L]
      rw [show
        (fun n : ℕ => probeSharpCollarBaseLayerScale M E
          (collarBandMeanDepth M E) n) =
            fun n : ℕ => (C * B) * whitneyDecayRatio ^ n by
        funext n
        rw [probeSharpCollarBaseLayerScale]
        dsimp only [C, B]
        ring]
      rw [tsum_mul_left,
        tsum_geometric_of_norm_lt_one norm_whitneyDecayRatio_lt_one]
    rw [hsum]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB hC0) hinv0
  have hP : P ≤ KP := by
    simpa only [P, KP] using
      probeSharpCollarBasePowerScale_le_profileCube
        M hsigma0 hsigma hgammaB
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact probeSharpCollarBandMeanPowerScale_nonneg M sigma
  have hLDZ0 : 0 ≤ C * (D * Z) * (1 - whitneyDecayRatio)⁻¹ :=
    mul_nonneg
      (mul_nonneg hC0 (mul_nonneg (by positivity) (Real.exp_pos _).le))
      hinv0
  have hLP : L * P ≤
      (C * (D * Z) * (1 - whitneyDecayRatio)⁻¹) * KP :=
    mul_le_mul hL hP hP0 hLDZ0
  rw [probeSharpCollarBaseTraceScale,
    probeSharpCollarBaseCoordinateScale]
  change (d : ℝ) * (L * P) ≤ _
  calc
    (d : ℝ) * (L * P) ≤
        (d : ℝ) *
          ((C * (D * Z) * (1 - whitneyDecayRatio)⁻¹) * KP) :=
      mul_le_mul_of_nonneg_left hLP (Nat.cast_nonneg d)
    _ = probeSharpCollarBaseTunedTracePrefactor d * Z := by
      rw [probeSharpCollarBaseTunedTracePrefactor]
      dsimp only [C, D, KP]
      ring

private theorem probeSharpCollarBaseTuned_output_choice
    {Cup : ℝ} (houtput : probeSharpCollarBaseTunedOutputConst d ≤ Cup) :
    probeSharpCollarBaseTunedTracePrefactor d + 8 ≤
      (collarBandMeanDepthCoeff d / 36) * Cup := by
  let rate : ℝ := collarBandMeanDepthCoeff d / 36
  have hbranch : 1 + (probeSharpCollarBaseTunedTracePrefactor d + 8) *
      rate⁻¹ ≤ Cup := by
    calc
      _ ≤ max (collarBandMeanDepthThreshold d)
          (1 + (probeSharpCollarBaseTunedTracePrefactor d + 8) *
            rate⁻¹) := le_max_right _ _
      _ ≤ probeSharpCollarBaseTunedOutputConst d := by
        rw [probeSharpCollarBaseTunedOutputConst]
        exact le_max_right _ _
      _ ≤ Cup := houtput
  have hrate : 0 < rate := by
    dsimp only [rate]
    exact div_pos (collarBandMeanDepthCoeff_pos d) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hbranch hrate.le
  have hcancel : rate *
      ((probeSharpCollarBaseTunedTracePrefactor d + 8) * rate⁻¹) =
        probeSharpCollarBaseTunedTracePrefactor d + 8 := by
    field_simp [hrate.ne']
  change probeSharpCollarBaseTunedTracePrefactor d + 8 ≤ rate * Cup
  calc
    probeSharpCollarBaseTunedTracePrefactor d + 8 =
        rate * ((probeSharpCollarBaseTunedTracePrefactor d + 8) * rate⁻¹) :=
      hcancel.symm
    _ ≤ rate *
        (1 + (probeSharpCollarBaseTunedTracePrefactor d + 8) * rate⁻¹) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hrate.le
    _ ≤ rate * Cup := hmul

/-- The literal finite-coordinate collar-base trace at the common tuned depth
has the exact local per-descendant rare scale required by the upper assembly. -/
theorem isBigOWith_upperProfileTarget_probeSharpFramedCollarBaseTraceLane_tuned
    (M : ABKModel d) {m : ℤ} {k : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {sigma Cup : ℝ} (hsigma0 : 0 < sigma) (hsigma : sigma ≤ 1 / 2)
    (hmax : max (Real.exp (Cup / sigma))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEgamma : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (houtput : probeSharpCollarBaseTunedOutputConst d ≤ Cup) :
    IsBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma ((1 - sigma) / 3))
      (probeSharpFramedCollarBaseTraceLane M R (E : ℝ)
        (collarBandMeanDepth M (E : ℝ)))
      ((3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) *
        Real.exp (-(Cup⁻¹ *
          ((E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹))) ^ 8) := by
  have hd : 2 ≤ d := M.shellPrefix.dimension
  let X : ℝ := (E : ℝ)⁻¹ ^ 2 * M.gamma⁻¹
  let eps : ℝ := Real.exp (-(Cup⁻¹ * X))
  let rate : ℝ := collarBandMeanDepthCoeff d / 36
  let K : ℝ := probeSharpCollarBaseTunedTracePrefactor d
  have hCup0 : 0 < Cup :=
    (probeSharpCollarBaseTunedOutputConst_pos d).trans_le houtput
  have haux : profileAuxiliaryConst d ≤ Cup := by
    calc
      profileAuxiliaryConst d ≤ probeSharpCollarBaseTunedOutputConst d := by
        rw [probeSharpCollarBaseTunedOutputConst]
        exact le_max_left _ _
      _ ≤ Cup := houtput
  have hdepth : collarBandMeanDepthThreshold d ≤ Cup := by
    calc
      collarBandMeanDepthThreshold d ≤
          max (collarBandMeanDepthThreshold d)
            (1 + (probeSharpCollarBaseTunedTracePrefactor d + 8) *
              (collarBandMeanDepthCoeff d / 36)⁻¹) := le_max_left _ _
      _ ≤ probeSharpCollarBaseTunedOutputConst d := by
        rw [probeSharpCollarBaseTunedOutputConst]
        exact le_max_right _ _
      _ ≤ Cup := houtput
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
  have hlarge : collarBandMeanDepthThreshold d ≤ X := hdepth.trans hX
  have hgammaB : M.gamma ≤ bfaProfileB := by
    calc
      M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) := hgamma
      _ ≤ (3 / 2 : ℝ) * bfaProfileB * sigma :=
        zpow_neg_five_le_three_halves_mul_bfaProfileB_of_profileAuxiliaryGate
          hsigma0 ((le_max_left _ _).trans hmaxAux)
      _ ≤ (3 / 2 : ℝ) * bfaProfileB * (1 / 2) :=
        mul_le_mul_of_nonneg_left hsigma
          (mul_nonneg (by norm_num) bfaProfileB_pos.le)
      _ ≤ bfaProfileB := by
        nlinarith [bfaProfileB_pos]
  have hraw :=
    isBigOWith_upperProfileTarget_probeSharpFramedCollarBaseTraceLane
      hd M hR hS hsigma0 hsigma hmaxAux hEgamma
        (collarBandMeanDepth M (E : ℝ))
  have hscaleExp :
      probeSharpCollarBaseTraceScale d M (E : ℝ) sigma
          (collarBandMeanDepth M (E : ℝ)) ≤
        K * Real.exp (-(rate * X)) := by
    simpa only [K, rate, X] using
      probeSharpCollarBaseTraceScale_tuned_le_exp hd M
        (lt_of_lt_of_le zero_lt_one E.property)
        hsigma0 hsigma hgammaB hlarge
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact probeSharpCollarBaseTunedTracePrefactor_nonneg hd
  have hchoice : K + 8 ≤ rate * Cup := by
    simpa only [K, rate] using
      probeSharpCollarBaseTuned_output_choice houtput
  have habsorb : K * Real.exp (-(rate * X)) ≤ eps ^ 8 := by
    dsimp only [eps]
    exact prefactor_mul_exp_le_frozenRare_pow hK0 hCup0 hX hchoice
  have hpow : 1 ≤ (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity))
  have heps0 : 0 ≤ eps ^ 8 := pow_nonneg (Real.exp_pos _).le 8
  have hscale :
      probeSharpCollarBaseTraceScale d M (E : ℝ) sigma
          (collarBandMeanDepth M (E : ℝ)) ≤
        (3 : ℝ) ^ (M.gamma * ((k : ℝ) + 1)) * eps ^ 8 :=
    hscaleExp.trans (habsorb.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow heps0))
  have hfinal := hraw.mono_scale hscale
  simpa only [upperProfileTargetSigma, eps, X, mul_assoc] using hfinal

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
