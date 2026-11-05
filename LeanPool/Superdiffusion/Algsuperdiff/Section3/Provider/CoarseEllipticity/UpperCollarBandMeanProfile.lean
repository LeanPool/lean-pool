/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperBandMeanShiftProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperProfileProducts
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.BfaPerCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedLayerNamedDecomposition

/-!
# UpperCollarBandMeanProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Literal collar profile for the tuned band mean

This file prices the collar copy of the deterministic deep-band mean in one
framed Whitney layer.  The carrier is the literal ninth summand of
`probeSharpFramedLayerNamedSum`: it retains the collar gradient factor, the
square root of the actual `assemblyBad` minimum, and the descendant frame.

The load-bearing estimate uses both branches of `assemblyBad`.  The bad mass
is first bounded by the geometric mean of its density cap and its layer-mass
cap; taking the square root already present in the wave lane therefore costs a
fourth root.  This leaves a summable `3^(-n/8)` Whitney profile after the
literal collar growth is paid.  No domination proposition is supplied by a
caller.

The deterministic cap scale is deliberately not absorbed here.  In particular
its factor at the tuned depth `waveBandDepth 1 E gamma` remains visible, so
later code cannot silently assume that the percolation rate pays the fixed
collar slope.  These are internal Provider declarations and make no source-node
or development-status claim.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Affine
open Algsuperdiff.Section3.Provider.Multiscale
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-- The density cap with its decreasing `hsep` contribution enlarged at
`hsep = 0`.  It is deterministic and keeps both density mechanisms visible. -/
def probeSharpCollarBandMeanCapEnvelope
    (M : ABKModel d) (E : ℝ) (k₀ : ℕ) : ℝ :=
  9 * (99 : ℝ) ^ d *
    (Real.exp (-(siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))) +
      (3 : ℝ) ^ (-((k₀ : ℝ) / 2)))

/-- The fourth root of the deterministic collar cap. -/
def probeSharpCollarBandMeanCapQuarter
    (M : ABKModel d) (E : ℝ) (k₀ : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (probeSharpCollarBandMeanCapEnvelope M E k₀))

/-- The dimension-only fourth root of the Whitney mass prefactor. -/
def probeSharpCollarBandMeanMassQuarterConst (d : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (6 * (d : ℝ)))

/-- The exact collar/frame core multiplying the deterministic band square in
one translated strict-descendant layer. -/
def probeSharpCollarBandMeanLayerCore
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k₀ n : ℕ) (i : ℤ)
    (Cgrad : ℝ) (omega : CutoffSample d) : ℝ :=
  probeSharpFramedCollarFactor M root E bfaProfileB k₀ n Cgrad omega *
    Real.sqrt (assemblyBad M E (hsep M root E bfaProfileB omega) k₀ n) *
    probeSharpFramedAfterBandMultiplier
      M root E bfaProfileB k₀ n i omega


/-- A dimension-only bound for the deterministic band coefficient. -/
def probeSharpCollarBandMeanOuterConst (d : ℕ) : ℝ :=
  5 * (d : ℝ) ^ 2 * probeSharpBandMeanDimensionConst d *
    waveBandConst (probeDeepBandMeanAmplitude d)


theorem probeSharpCollarBandMeanCapEnvelope_nonneg
    (M : ABKModel d) (E : ℝ) (k₀ : ℕ) :
    0 ≤ probeSharpCollarBandMeanCapEnvelope M E k₀ := by
  rw [probeSharpCollarBandMeanCapEnvelope]
  positivity

theorem probeSharpCollarBandMeanCapQuarter_nonneg
    (M : ABKModel d) (E : ℝ) (k₀ : ℕ) :
    0 ≤ probeSharpCollarBandMeanCapQuarter M E k₀ := by
  rw [probeSharpCollarBandMeanCapQuarter]
  positivity

theorem probeSharpCollarBandMeanMassQuarterConst_nonneg (d : ℕ) :
    0 ≤ probeSharpCollarBandMeanMassQuarterConst d := by
  rw [probeSharpCollarBandMeanMassQuarterConst]
  positivity

theorem probeSharpCollarBandMeanLayerCore_nonneg
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k₀ n : ℕ) (i : ℤ)
    (Cgrad : ℝ) (omega : CutoffSample d) :
    0 ≤ probeSharpCollarBandMeanLayerCore
      M root E k₀ n i Cgrad omega := by
  rw [probeSharpCollarBandMeanLayerCore]
  exact mul_nonneg
    (mul_nonneg
      (probeSharpFramedCollarFactor_nonneg
        M root E bfaProfileB k₀ n Cgrad omega)
      (Real.sqrt_nonneg _))
    (probeSharpFramedAfterBandMultiplier_nonneg
      M root E bfaProfileB k₀ n i omega)

theorem measurable_probeSharpCollarBandMeanLayerCore
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k₀ n : ℕ) (i : ℤ)
    (Cgrad : ℝ) :
    Measurable (probeSharpCollarBandMeanLayerCore
      M root E k₀ n i Cgrad) := by
  have hfactor : Measurable fun omega : CutoffSample d =>
      probeSharpFramedCollarFactor
        M root E bfaProfileB k₀ n Cgrad omega :=
    measurable_comp_hsep M root E bfaProfileB fun hs : ℕ =>
      4 * (Cgrad ^ 2 *
        (3 : ℝ) ^ (2 * (bfaProfileB * ((n : ℝ) +
          (whitneyScaleSeq bfaProfileB hs k₀ n : ℝ)))))
  have hbad : Measurable fun omega : CutoffSample d =>
      assemblyBad M E (hsep M root E bfaProfileB omega) k₀ n :=
    measurable_comp_hsep M root E bfaProfileB fun hs : ℕ =>
      assemblyBad M E hs k₀ n
  have hframe := measurable_probeSharpFramedAfterBandMultiplier
    M root E bfaProfileB k₀ n i
  exact (hfactor.mul hbad.sqrt).mul hframe


theorem probeSharpCollarBandMeanOuterConst_nonneg
    (hd : 2 ≤ d) :
    0 ≤ probeSharpCollarBandMeanOuterConst d := by
  rw [probeSharpCollarBandMeanOuterConst]
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (probeSharpBandMeanDimensionConst_nonneg hd))
    (waveBandConst_nonneg _)


/-- The random collar mass cap is bounded by the deterministic `hsep = 0`
envelope. -/
theorem collarMassCap_le_probeSharpCollarBandMeanCapEnvelope
    (M : ABKModel d) (E : ℝ) (hs k₀ : ℕ) :
    collarMassCap M E hs k₀ ≤
      probeSharpCollarBandMeanCapEnvelope M E k₀ := by
  have hpow : (3 : ℝ) ^ (-(((hs : ℝ) + (k₀ : ℝ)) / 2)) ≤
      (3 : ℝ) ^ (-((k₀ : ℝ) / 2)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hhs : (0 : ℝ) ≤ (hs : ℝ) := Nat.cast_nonneg hs
    linarith
  have hpref : 0 ≤ 9 * (99 : ℝ) ^ d := by positivity
  rw [collarMassCap, probeSharpCollarBandMeanCapEnvelope]
  exact mul_le_mul_of_nonneg_left (by linarith) hpref

/-- at the square-root collar-wave carrier: using both branches of `assemblyBad`
gives a fourth-root cap/mass interpolation. -/
theorem sqrt_assemblyBad_le_collarBandMean_fourthRoot
    (M : ABKModel d) (E : ℝ) (hs k₀ n : ℕ) :
    Real.sqrt (assemblyBad M E hs k₀ n) ≤
      Real.sqrt (Real.sqrt
        (probeSharpCollarBandMeanCapEnvelope M E k₀ *
          probeSharpLayerMassEnvelope d n)) := by
  have hcap0 := probeSharpCollarBandMeanCapEnvelope_nonneg M E k₀
  have hmass0 : 0 ≤ probeSharpLayerMassEnvelope d n := by
    rw [probeSharpLayerMassEnvelope]
    positivity
  have hbadCap : assemblyBad M E hs k₀ n ≤
      probeSharpCollarBandMeanCapEnvelope M E k₀ :=
    (assemblyBad_le_cap M E hs k₀ n).trans
      (collarMassCap_le_probeSharpCollarBandMeanCapEnvelope M E hs k₀)
  have hbadMass : assemblyBad M E hs k₀ n ≤
      probeSharpLayerMassEnvelope d n := by
    simpa only [probeSharpLayerMassEnvelope] using
      assemblyBad_le_mass M E hs k₀ n
  have hinterp : assemblyBad M E hs k₀ n ≤
      Real.sqrt
        (probeSharpCollarBandMeanCapEnvelope M E k₀ *
          probeSharpLayerMassEnvelope d n) :=
    (le_min hbadCap hbadMass).trans (min_le_sqrt_mul hcap0 hmass0)
  exact Real.sqrt_le_sqrt hinterp

private theorem sqrt_sqrt_mul_of_nonneg {a b : ℝ}
    (ha : 0 ≤ a) :
    Real.sqrt (Real.sqrt (a * b)) =
      Real.sqrt (Real.sqrt a) * Real.sqrt (Real.sqrt b) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul (Real.sqrt_nonneg a)]

/-- Exact fourth-root form of the Whitney mass profile. -/
theorem sqrt_sqrt_probeSharpLayerMassEnvelope_eq (d n : ℕ) :
    Real.sqrt (Real.sqrt (probeSharpLayerMassEnvelope d n)) =
      probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (-(n : ℝ) / 4) := by
  have hmass : 0 ≤ 6 * (d : ℝ) := by positivity
  rw [probeSharpLayerMassEnvelope, Real.sqrt_mul hmass,
    Real.sqrt_mul (Real.sqrt_nonneg (6 * (d : ℝ))),
    probeSharpCollarBandMeanMassQuarterConst]
  congr 1
  rw [sqrt_three_rpow, sqrt_three_rpow]
  congr 1
  ring

/-- The interpolated fourth root splits into the deterministic cap quarter
and the exact geometric Whitney profile. -/
theorem collarBandMean_fourthRoot_eq
    (M : ABKModel d) (E : ℝ) (k₀ n : ℕ) :
    Real.sqrt (Real.sqrt
        (probeSharpCollarBandMeanCapEnvelope M E k₀ *
          probeSharpLayerMassEnvelope d n)) =
      probeSharpCollarBandMeanCapQuarter M E k₀ *
        probeSharpCollarBandMeanMassQuarterConst d *
        (3 : ℝ) ^ (-(n : ℝ) / 4) := by
  rw [sqrt_sqrt_mul_of_nonneg
    (probeSharpCollarBandMeanCapEnvelope_nonneg M E k₀),
    probeSharpCollarBandMeanCapQuarter,
    sqrt_sqrt_probeSharpLayerMassEnvelope_eq]
  ring

/-- The literal ninth named summand is exactly the deterministic band
coefficient times the collar/frame core. -/
theorem probeSharpFramedCollarWavePart_bandMean_eq
    (M : ABKModel d) (root : ℤ) (E : ℝ) (k₀ n : ℕ) (i : ℤ)
    (j : Fin d) (Cgrad : ℝ) (omega : CutoffSample d) :
    probeSharpFramedCollarWavePart M root E bfaProfileB k₀ n i
        (basisVec j) Cgrad
        (fun _eta => waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2)
        omega =
      (probeMeanGoodWaveConst M * vecNormSq (basisVec j) *
        (5 * (d : ℝ) ^ 2 *
          waveBandMean (probeDeepBandMeanAmplitude d) M.gamma k₀ ^ 2)) *
        probeSharpCollarBandMeanLayerCore
          M root E k₀ n i Cgrad omega := by
  rw [probeSharpFramedCollarWavePart,
    probeSharpCollarBandMeanLayerCore]
  ring


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
