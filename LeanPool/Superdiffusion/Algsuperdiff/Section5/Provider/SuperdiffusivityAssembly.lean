/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepOneMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.StreamProcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.SuperdiffusiveBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.IntrinsicScale
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ParameterizedProcessSemigroup

/-!
# SuperdiffusivityAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Annealed assembly of the reachable superdiffusive bounds

This file carries out the measure-theoretic last step from quenched displacement estimates at a
random confinement scale.  The input structure names the two quenched comparisons, the second-
and fourth-order moments of the renormalization error, and the fourth-order moment of the
confinement radius.  In an application, the first two fields are supplied after the process
moment, rare-exit, and stopping-time-removal estimates have been combined.

The Cauchy--Schwarz splits use exponents `2p` for the first comparison and `4p, 4p, 2p` for the
second comparison.  Thus the separately available random-radius estimate contributes one power
of `|log gamma|`.  The resulting powers are `4` and `7`; no claim with the smaller powers is made
here.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.Homogenization
open Algsuperdiff.Section5.Field
open Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form
open HCPolySupport MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

private theorem lintegral_mul_rpow_le_of_moments (mu : Measure Omega)
    {F G : Omega → ℝ≥0∞} {RF RG p : ℝ} (hp : 0 ≤ p)
    (hF : AEMeasurable F mu) (hG : AEMeasurable G mu)
    (hRF : 0 ≤ RF)
    (hFm : (∫⁻ omega, F omega ^ (2 * p) ∂mu) ≤ ENNReal.ofReal RF ^ (2 * p))
    (hGm : (∫⁻ omega, G omega ^ (2 * p) ∂mu) ≤ ENNReal.ofReal RG ^ (2 * p)) :
    (∫⁻ omega, (F omega * G omega) ^ p ∂mu) ≤ ENNReal.ofReal (RF * RG) ^ p := by
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq mu Real.HolderConjugate.two_two
    (hF.pow_const p) (hG.pow_const p)
  have hFpow : (∫⁻ omega, (F omega ^ p) ^ (2 : ℝ) ∂mu) =
      ∫⁻ omega, F omega ^ (2 * p) ∂mu := by
    refine lintegral_congr fun omega => ?_
    rw [← ENNReal.rpow_mul]
    ring_nf
  have hGpow : (∫⁻ omega, (G omega ^ p) ^ (2 : ℝ) ∂mu) =
      ∫⁻ omega, G omega ^ (2 * p) ∂mu := by
    refine lintegral_congr fun omega => ?_
    rw [← ENNReal.rpow_mul]
    ring_nf
  have hFroot : (∫⁻ omega, (F omega ^ p) ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal RF ^ p := by
    rw [hFpow]
    refine (ENNReal.rpow_le_rpow hFm (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq ?_
    rw [← ENNReal.rpow_mul]
    ring_nf
  have hGroot : (∫⁻ omega, (G omega ^ p) ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal RG ^ p := by
    rw [hGpow]
    refine (ENNReal.rpow_le_rpow hGm (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq ?_
    rw [← ENNReal.rpow_mul]
    ring_nf
  calc
    (∫⁻ omega, (F omega * G omega) ^ p ∂mu) =
        ∫⁻ omega, F omega ^ p * G omega ^ p ∂mu := by
          refine lintegral_congr fun omega => ?_
          exact ENNReal.mul_rpow_of_nonneg _ _ hp
    _ ≤ (∫⁻ omega, (F omega ^ p) ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) *
          (∫⁻ omega, (G omega ^ p) ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) := hholder
    _ ≤ ENNReal.ofReal RF ^ p * ENNReal.ofReal RG ^ p :=
      mul_le_mul hFroot hGroot (by positivity) (by positivity)
    _ = ENNReal.ofReal (RF * RG) ^ p := by
      rw [ENNReal.ofReal_mul hRF, ENNReal.mul_rpow_of_nonneg _ _ hp]

private theorem lintegral_sq_rpow_le_of_moment {mu : Measure Omega}
    {F : Omega → ℝ≥0∞} {RF p : ℝ} (hRF : 0 ≤ RF)
    (hFm : (∫⁻ omega, F omega ^ (2 * p) ∂mu) ≤ ENNReal.ofReal RF ^ (2 * p)) :
    (∫⁻ omega, (F omega ^ (2 : ℝ)) ^ p ∂mu) ≤
      ENNReal.ofReal (RF ^ (2 : ℕ)) ^ p := by
  calc
    (∫⁻ omega, (F omega ^ (2 : ℝ)) ^ p ∂mu) =
        ∫⁻ omega, F omega ^ (2 * p) ∂mu := by
          refine lintegral_congr fun omega => ?_
          rw [← ENNReal.rpow_mul]
    _ ≤ ENNReal.ofReal RF ^ (2 * p) := hFm
    _ = ENNReal.ofReal (RF ^ (2 : ℕ)) ^ p := by
      rw [ENNReal.ofReal_pow hRF, ← ENNReal.rpow_natCast]
      rw [← ENNReal.rpow_mul]
      norm_num

private theorem lintegral_const_mul_rpow_le {mu : Measure Omega}
    {F : Omega → ℝ≥0∞} {A RF p : ℝ} (hp : 0 ≤ p) (hA : 0 ≤ A)
    (hFm : (∫⁻ omega, F omega ^ p ∂mu) ≤ ENNReal.ofReal RF ^ p) :
    (∫⁻ omega, (ENNReal.ofReal A * F omega) ^ p ∂mu) ≤
      ENNReal.ofReal (A * RF) ^ p := by
  calc
    (∫⁻ omega, (ENNReal.ofReal A * F omega) ^ p ∂mu) =
        ∫⁻ omega, ENNReal.ofReal A ^ p * F omega ^ p ∂mu := by
          refine lintegral_congr fun omega => ?_
          exact ENNReal.mul_rpow_of_nonneg _ _ hp
    _ = ENNReal.ofReal A ^ p * ∫⁻ omega, F omega ^ p ∂mu :=
      lintegral_const_mul' _ _
        (ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal A ^ p * ENNReal.ofReal RF ^ p := mul_le_mul_right hFm _
    _ = ENNReal.ofReal (A * RF) ^ p := by
      rw [ENNReal.ofReal_mul hA, ENNReal.mul_rpow_of_nonneg _ _ hp]

/-! ## The component interface -/

/-- Named inputs for the annealed assembly at one model, time, and exponent.

The `confinementRadius` is `3^m_t` in the intended application.  The two pointwise fields are
the outputs of the quenched stopped-moment assembly after the C2 process moments, the bad-event
bound, and the C4/C6 removal estimates have been supplied.  The remaining three fields are the
random-scale estimates used by the two Holder splits. -/
structure SuperdiffusivityV2Components {d : ℕ} [NeZero d]
    (M : ABKModel d) (cstar t p C0 : ℝ) where
  renormalizationError : FullSample d M.gamma → ℝ
  confinementRadius : FullSample d M.gamma → ℝ
  renormalizationError_nonneg : ∀ omega, 0 ≤ renormalizationError omega
  confinementRadius_nonneg : ∀ omega, 0 ≤ confinementRadius omega
  renormalizationError_aemeasurable :
    AEMeasurable renormalizationError (fullSampleLaw M).toMeasure
  confinementRadius_aemeasurable :
    AEMeasurable confinementRadius (fullSampleLaw M).toMeasure
  secondMoment_quenched : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
    (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
     letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
     |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
          ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
              ((0 : Vec d) : OnePoint (Vec d)))) -
        2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2|) ≤
      C0 * (renormalizationError omega +
        Real.sqrt M.gamma * |Real.log M.gamma|) * confinementRadius omega ^ 2
  meanSq_quenched : ∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
    (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
     letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
     vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
          ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
              ((0 : Vec d) : OnePoint (Vec d))))) ≤
      C0 * (renormalizationError omega ^ 2 + M.gamma ^ (80 : ℕ)) *
        confinementRadius omega ^ 2
  renormalizationError_moment_two :
    (∫⁻ omega, ENNReal.ofReal (renormalizationError omega) ^ (2 * p)
        ∂(fullSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (C0 * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ (2 * p)
  renormalizationError_moment_four :
    (∫⁻ omega, ENNReal.ofReal (renormalizationError omega) ^ (4 * p)
        ∂(fullSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (C0 * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ (4 * p)
  confinementRadius_moment_four :
    (∫⁻ omega, ENNReal.ofReal (confinementRadius omega) ^ (4 * p)
        ∂(fullSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (C0 * Real.sqrt |Real.log M.gamma| *
        intrinsicScale M.nu cstar M.gamma t) ^ (4 * p)

private theorem annealed_v2_bounds_of_components {d : ℕ} [NeZero d]
    (M : ABKModel d) {cstar t p C0 : ℝ} (hcstar : 0 < cstar) (ht : 0 < t)
    (hp : 1 ≤ p) (hC0 : 0 ≤ C0)
    (H : SuperdiffusivityV2Components M cstar t p C0) :
    let L := |Real.log M.gamma|
    let Fp := Real.sqrt p + Real.sqrt L
    let R := intrinsicScale M.nu cstar M.gamma t
    (∫⁻ omega : FullSample d M.gamma,
        (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
         letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
         ENNReal.ofReal
            |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
                ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                    ((0 : Vec d) : OnePoint (Vec d)))) -
              2 * (d : ℝ) * R ^ 2| ^ p)
        ∂(fullSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (C0 *
        (C0 * Fp * Real.sqrt M.gamma * L ^ (3 : ℕ) *
            (C0 * Real.sqrt L * R) ^ (2 : ℕ) +
          (Real.sqrt M.gamma * L) * (C0 * Real.sqrt L * R) ^ (2 : ℕ))) ^ p ∧
    (∫⁻ omega : FullSample d M.gamma,
        (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
         letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
         ENNReal.ofReal
            (vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
                ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                    ((0 : Vec d) : OnePoint (Vec d))))) ^ p)
        ∂(fullSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (C0 *
        ((C0 * Fp * Real.sqrt M.gamma * L ^ (3 : ℕ)) ^ (2 : ℕ) *
            (C0 * Real.sqrt L * R) ^ (2 : ℕ) +
          M.gamma ^ (80 : ℕ) * (C0 * Real.sqrt L * R) ^ (2 : ℕ))) ^ p := by
  dsimp only
  let mu := (fullSampleLaw M).toMeasure
  let E : FullSample d M.gamma → ℝ≥0∞ := fun omega =>
    ENNReal.ofReal (H.renormalizationError omega)
  let S : FullSample d M.gamma → ℝ≥0∞ := fun omega =>
    ENNReal.ofReal (H.confinementRadius omega)
  let S2 : FullSample d M.gamma → ℝ≥0∞ := fun omega => S omega ^ (2 : ℝ)
  let RE := C0 * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
    |Real.log M.gamma| ^ (3 : ℕ)
  let RS := C0 * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hEmeas : AEMeasurable E mu := H.renormalizationError_aemeasurable.ennreal_ofReal
  have hSmeas : AEMeasurable S mu := H.confinementRadius_aemeasurable.ennreal_ofReal
  have hS2meas : AEMeasurable S2 mu := hSmeas.pow_const 2
  have hRE0 : 0 ≤ RE := by
    dsimp only [RE]
    positivity
  have hRS0 : 0 ≤ RS := by
    dsimp only [RS]
    exact mul_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg _))
      (intrinsicScale_pos M.nu_pos hcstar M.shellPrefix.gamma_pos ht).le
  have hEm2 : (∫⁻ omega, E omega ^ (2 * p) ∂mu) ≤ ENNReal.ofReal RE ^ (2 * p) := by
    exact H.renormalizationError_moment_two
  have hEm4 : (∫⁻ omega, E omega ^ (4 * p) ∂mu) ≤ ENNReal.ofReal RE ^ (4 * p) := by
    exact H.renormalizationError_moment_four
  have hSm4 : (∫⁻ omega, S omega ^ (4 * p) ∂mu) ≤ ENNReal.ofReal RS ^ (4 * p) := by
    exact H.confinementRadius_moment_four
  have hS2m2 : (∫⁻ omega, S2 omega ^ (2 * p) ∂mu) ≤
      ENNReal.ofReal (RS ^ (2 : ℕ)) ^ (2 * p) := by
    have h := lintegral_sq_rpow_le_of_moment (mu := mu) (F := S) (RF := RS)
      (p := 2 * p) hRS0
    apply h
    convert hSm4 using 1 <;> ring_nf
  have hS2mp : (∫⁻ omega, S2 omega ^ p ∂mu) ≤
      ENNReal.ofReal (RS ^ (2 : ℕ)) ^ p :=
    lintegral_rpow_le_of_exponent_le hS2meas (lt_of_lt_of_le zero_lt_one hp)
      (by linarith only [hp]) hS2m2
  have hES2 : (∫⁻ omega, (E omega * S2 omega) ^ p ∂mu) ≤
      ENNReal.ofReal (RE * RS ^ (2 : ℕ)) ^ p :=
    lintegral_mul_rpow_le_of_moments mu hp0 hEmeas hS2meas hRE0 hEm2 hS2m2
  have hE2m2 : (∫⁻ omega, (E omega ^ (2 : ℝ)) ^ (2 * p) ∂mu) ≤
      ENNReal.ofReal (RE ^ (2 : ℕ)) ^ (2 * p) := by
    have h := lintegral_sq_rpow_le_of_moment (mu := mu) (F := E) (RF := RE)
      (p := 2 * p) hRE0
    apply h
    convert hEm4 using 1 <;> ring_nf
  have hE2S2 : (∫⁻ omega, ((E omega ^ (2 : ℝ)) * S2 omega) ^ p ∂mu) ≤
      ENNReal.ofReal (RE ^ (2 : ℕ) * RS ^ (2 : ℕ)) ^ p :=
    lintegral_mul_rpow_le_of_moments mu hp0 (hEmeas.pow_const 2) hS2meas
      (sq_nonneg RE) hE2m2 hS2m2
  let A := Real.sqrt M.gamma * |Real.log M.gamma|
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hAS2 : (∫⁻ omega, (ENNReal.ofReal A * S2 omega) ^ p ∂mu) ≤
      ENNReal.ofReal (A * RS ^ (2 : ℕ)) ^ p :=
    lintegral_const_mul_rpow_le hp0 hA0 hS2mp
  have hgamma80 : 0 ≤ M.gamma ^ (80 : ℕ) := pow_nonneg M.shellPrefix.gamma_pos.le _
  have hgammaS2 :
      (∫⁻ omega, (ENNReal.ofReal (M.gamma ^ (80 : ℕ)) * S2 omega) ^ p ∂mu) ≤
        ENNReal.ofReal (M.gamma ^ (80 : ℕ) * RS ^ (2 : ℕ)) ^ p :=
    lintegral_const_mul_rpow_le hp0 hgamma80 hS2mp
  have hfirstSum := lintegral_rpow_add_le_of_moments hp
    (hEmeas.mul hS2meas) (aemeasurable_const.mul hS2meas)
    (mul_nonneg hRE0 (sq_nonneg RS)) (mul_nonneg hA0 (sq_nonneg RS)) hES2 hAS2
  have hsecondSum := lintegral_rpow_add_le_of_moments hp
    ((hEmeas.pow_const 2).mul hS2meas) (aemeasurable_const.mul hS2meas)
    (mul_nonneg (sq_nonneg RE) (sq_nonneg RS))
    (mul_nonneg hgamma80 (sq_nonneg RS)) hE2S2 hgammaS2
  constructor
  · calc
      (∫⁻ omega : FullSample d M.gamma,
          (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
           letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
           ENNReal.ofReal
              |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
                  ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                      ((0 : Vec d) : OnePoint (Vec d)))) -
                2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2| ^ p)
          ∂(fullSampleLaw M).toMeasure) ≤
          ∫⁻ omega, (ENNReal.ofReal C0 *
            (E omega * S2 omega + ENNReal.ofReal A * S2 omega)) ^ p ∂mu := by
              refine lintegral_mono_ae (H.secondMoment_quenched.mono fun omega homega => ?_)
              refine ENNReal.rpow_le_rpow ?_ hp0
              have hreal :
                  |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
                      ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                          ((0 : Vec d) : OnePoint (Vec d)))) -
                    2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2| ≤
                    C0 * (H.renormalizationError omega * H.confinementRadius omega ^ 2) +
                      C0 * ((Real.sqrt M.gamma * |Real.log M.gamma|) *
                        H.confinementRadius omega ^ 2) := by
                calc
                  _ ≤ C0 * (H.renormalizationError omega +
                        Real.sqrt M.gamma * |Real.log M.gamma|) *
                      H.confinementRadius omega ^ 2 := homega
                  _ = _ := by ring
              refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
              dsimp only [E, S2, S, A]
              rw [ENNReal.ofReal_add
                    (mul_nonneg hC0 (mul_nonneg (H.renormalizationError_nonneg omega)
                      (sq_nonneg (H.confinementRadius omega))))
                    (mul_nonneg hC0 (mul_nonneg hA0
                      (sq_nonneg (H.confinementRadius omega)))),
                ENNReal.ofReal_mul hC0, ENNReal.ofReal_mul hC0,
                ENNReal.ofReal_mul (H.renormalizationError_nonneg omega),
                ENNReal.ofReal_mul hA0,
                ENNReal.ofReal_pow (H.confinementRadius_nonneg omega)]
              rw [← ENNReal.rpow_natCast]
              rw [show A = Real.sqrt M.gamma * |Real.log M.gamma| by rfl]
              exact (mul_add (ENNReal.ofReal C0)
                (ENNReal.ofReal (H.renormalizationError omega) *
                  ENNReal.ofReal (H.confinementRadius omega) ^ (2 : ℝ))
                (ENNReal.ofReal (Real.sqrt M.gamma * |Real.log M.gamma|) *
                  ENNReal.ofReal (H.confinementRadius omega) ^ (2 : ℝ))).symm
      _ ≤ ENNReal.ofReal C0 ^ p *
          ENNReal.ofReal (RE * RS ^ (2 : ℕ) + A * RS ^ (2 : ℕ)) ^ p := by
            rw [lintegral_congr fun omega => ENNReal.mul_rpow_of_nonneg _ _ hp0,
              lintegral_const_mul' _ _
                (ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top)]
            exact mul_le_mul_right hfirstSum _
      _ = ENNReal.ofReal (C0 *
          (RE * RS ^ (2 : ℕ) + A * RS ^ (2 : ℕ))) ^ p := by
            rw [ENNReal.ofReal_mul hC0, ENNReal.mul_rpow_of_nonneg _ _ hp0]
  · calc
      (∫⁻ omega : FullSample d M.gamma,
          (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
           letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
           ENNReal.ofReal
              (vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
                  ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                      ((0 : Vec d) : OnePoint (Vec d))))) ^ p)
          ∂(fullSampleLaw M).toMeasure) ≤
          ∫⁻ omega, (ENNReal.ofReal C0 *
            ((E omega ^ (2 : ℝ)) * S2 omega +
              ENNReal.ofReal (M.gamma ^ (80 : ℕ)) * S2 omega)) ^ p ∂mu := by
              refine lintegral_mono_ae (H.meanSq_quenched.mono fun omega homega => ?_)
              refine ENNReal.rpow_le_rpow ?_ hp0
              have hreal :
                  vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
                      ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                          ((0 : Vec d) : OnePoint (Vec d)))) ≤
                    C0 * (H.renormalizationError omega ^ 2 *
                        H.confinementRadius omega ^ 2) +
                      C0 * (M.gamma ^ (80 : ℕ) * H.confinementRadius omega ^ 2) := by
                calc
                  _ ≤ C0 * (H.renormalizationError omega ^ 2 + M.gamma ^ 80) *
                      H.confinementRadius omega ^ 2 := homega
                  _ = _ := by ring
              refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
              dsimp only [E, S2, S]
              rw [ENNReal.ofReal_add
                    (mul_nonneg hC0 (mul_nonneg (sq_nonneg _)
                      (sq_nonneg (H.confinementRadius omega))))
                    (mul_nonneg hC0 (mul_nonneg hgamma80
                      (sq_nonneg (H.confinementRadius omega)))),
                ENNReal.ofReal_mul hC0, ENNReal.ofReal_mul hC0,
                ENNReal.ofReal_mul (sq_nonneg (H.renormalizationError omega)),
                ENNReal.ofReal_mul hgamma80,
                ENNReal.ofReal_pow (H.renormalizationError_nonneg omega),
                ENNReal.ofReal_pow (H.confinementRadius_nonneg omega)]
              rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast]
              exact (mul_add (ENNReal.ofReal C0)
                (ENNReal.ofReal (H.renormalizationError omega) ^ (2 : ℝ) *
                  ENNReal.ofReal (H.confinementRadius omega) ^ (2 : ℝ))
                (ENNReal.ofReal (M.gamma ^ (80 : ℕ)) *
                  ENNReal.ofReal (H.confinementRadius omega) ^ (2 : ℝ))).symm
      _ ≤ ENNReal.ofReal C0 ^ p *
          ENNReal.ofReal (RE ^ (2 : ℕ) * RS ^ (2 : ℕ) +
            M.gamma ^ (80 : ℕ) * RS ^ (2 : ℕ)) ^ p := by
            rw [lintegral_congr fun omega => ENNReal.mul_rpow_of_nonneg _ _ hp0,
              lintegral_const_mul' _ _
                (ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top)]
            exact mul_le_mul_right hsecondSum _
      _ = ENNReal.ofReal (C0 *
          (RE ^ (2 : ℕ) * RS ^ (2 : ℕ) +
            M.gamma ^ (80 : ℕ) * RS ^ (2 : ℕ))) ^ p := by
            rw [ENNReal.ofReal_mul hC0, ENNReal.mul_rpow_of_nonneg _ _ hp0]

/-! ## Numerical absorption -/

private theorem first_v2_amplitude_le {C0 F G L R : ℝ}
    (hC0 : 1 ≤ C0) (hF : 1 ≤ F) (hG : 0 ≤ G) (hL : 1 ≤ L) (hR : 0 ≤ R) :
    C0 * (C0 * F * G * L ^ (3 : ℕ) * (C0 * Real.sqrt L * R) ^ (2 : ℕ) +
      (G * L) * (C0 * Real.sqrt L * R) ^ (2 : ℕ)) ≤
      (2 * C0 ^ (4 : ℕ)) * F * G * L ^ (4 : ℕ) * R ^ (2 : ℕ) := by
  have hC00 : 0 ≤ C0 := zero_le_one.trans hC0
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hsqrt : (Real.sqrt L) ^ (2 : ℕ) = L := Real.sq_sqrt hL0
  have hCpow : C0 ^ (3 : ℕ) ≤ C0 ^ (4 : ℕ) := by
    calc C0 ^ (3 : ℕ) ≤ C0 ^ (3 : ℕ) * C0 :=
          le_mul_of_one_le_right (pow_nonneg hC00 3) hC0
      _ = C0 ^ (4 : ℕ) := by ring
  have hLpow : L ^ (2 : ℕ) ≤ L ^ (4 : ℕ) := by
    calc L ^ (2 : ℕ) ≤ L ^ (2 : ℕ) * L ^ (2 : ℕ) :=
          le_mul_of_one_le_right (pow_nonneg hL0 2) (one_le_pow₀ hL)
      _ = L ^ (4 : ℕ) := by ring
  have hsmall : C0 ^ (3 : ℕ) * G * L ^ (2 : ℕ) * R ^ (2 : ℕ) ≤
      C0 ^ (4 : ℕ) * F * G * L ^ (4 : ℕ) * R ^ (2 : ℕ) := by
    calc
      C0 ^ (3 : ℕ) * G * L ^ (2 : ℕ) * R ^ (2 : ℕ) ≤
          C0 ^ (4 : ℕ) * G * L ^ (2 : ℕ) * R ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hCpow hG) (pow_nonneg hL0 2))
              (pow_nonneg hR 2)
      _ ≤ (C0 ^ (4 : ℕ) * G * L ^ (2 : ℕ) * R ^ (2 : ℕ)) * F :=
        le_mul_of_one_le_right (by positivity) hF
      _ ≤ (C0 ^ (4 : ℕ) * G * L ^ (4 : ℕ) * R ^ (2 : ℕ)) * F := by
        gcongr
      _ = C0 ^ (4 : ℕ) * F * G * L ^ (4 : ℕ) * R ^ (2 : ℕ) := by ring
  rw [show (C0 * Real.sqrt L * R) ^ (2 : ℕ) = C0 ^ (2 : ℕ) * L * R ^ (2 : ℕ)
    by rw [mul_pow, mul_pow, hsqrt]]
  calc
    C0 * (C0 * F * G * L ^ (3 : ℕ) * (C0 ^ (2 : ℕ) * L * R ^ (2 : ℕ)) +
        G * L * (C0 ^ (2 : ℕ) * L * R ^ (2 : ℕ))) =
        C0 ^ (4 : ℕ) * F * G * L ^ (4 : ℕ) * R ^ (2 : ℕ) +
          C0 ^ (3 : ℕ) * G * L ^ (2 : ℕ) * R ^ (2 : ℕ) := by ring
    _ ≤ C0 ^ (4 : ℕ) * F * G * L ^ (4 : ℕ) * R ^ (2 : ℕ) +
          C0 ^ (4 : ℕ) * F * G * L ^ (4 : ℕ) * R ^ (2 : ℕ) :=
      add_le_add_right hsmall _
    _ = (2 * C0 ^ (4 : ℕ)) * F * G * L ^ (4 : ℕ) * R ^ (2 : ℕ) := by ring

private theorem second_v2_amplitude_le {C0 F G gamma L R p : ℝ}
    (hC0 : 1 ≤ C0) (hp : 1 ≤ p) (_hF0 : 0 ≤ F)
    (hF2 : F ^ (2 : ℕ) ≤ 2 * (p + L)) (_hG : 0 ≤ G) (hG2 : G ^ (2 : ℕ) = gamma)
    (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) (hL : 1 ≤ L) (_hR : 0 ≤ R) :
    C0 * ((C0 * F * G * L ^ (3 : ℕ)) ^ (2 : ℕ) *
        (C0 * Real.sqrt L * R) ^ (2 : ℕ) +
      gamma ^ (80 : ℕ) * (C0 * Real.sqrt L * R) ^ (2 : ℕ)) ≤
      (3 * C0 ^ (5 : ℕ)) * (p + L) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) := by
  have hC00 : 0 ≤ C0 := zero_le_one.trans hC0
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hpL : 1 ≤ p + L := by linarith only [hp, hL]
  have hsqrt : (Real.sqrt L) ^ (2 : ℕ) = L := Real.sq_sqrt hL0
  have hgamma80 : gamma ^ (80 : ℕ) ≤ gamma := by
    rw [show (80 : ℕ) = 79 + 1 by norm_num, pow_succ]
    exact mul_le_of_le_one_left hgamma (pow_le_one₀ hgamma hgamma1)
  have hrough : C0 ^ (3 : ℕ) * gamma ^ (80 : ℕ) * L * R ^ (2 : ℕ) ≤
      C0 ^ (5 : ℕ) * (p + L) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) := by
    have hCpow : C0 ^ (3 : ℕ) ≤ C0 ^ (5 : ℕ) := by
      calc C0 ^ (3 : ℕ) ≤ C0 ^ (3 : ℕ) * C0 ^ (2 : ℕ) :=
            le_mul_of_one_le_right (pow_nonneg hC00 3) (one_le_pow₀ hC0)
        _ = C0 ^ (5 : ℕ) := by ring
    have hLpow : L ≤ L ^ (7 : ℕ) := by
      calc L ≤ L * L ^ (6 : ℕ) :=
            le_mul_of_one_le_right hL0 (one_le_pow₀ hL)
        _ = L ^ (7 : ℕ) := by ring
    calc
      C0 ^ (3 : ℕ) * gamma ^ (80 : ℕ) * L * R ^ (2 : ℕ) ≤
          C0 ^ (5 : ℕ) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) := by
            gcongr
      _ ≤ (C0 ^ (5 : ℕ) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ)) * (p + L) :=
        le_mul_of_one_le_right (by positivity) hpL
      _ = C0 ^ (5 : ℕ) * (p + L) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) := by ring
  rw [show (C0 * Real.sqrt L * R) ^ (2 : ℕ) = C0 ^ (2 : ℕ) * L * R ^ (2 : ℕ)
    by rw [mul_pow, mul_pow, hsqrt]]
  have hmain : C0 ^ (5 : ℕ) * F ^ (2 : ℕ) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) ≤
      2 * C0 ^ (5 : ℕ) * (p + L) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) := by
    have hleft : C0 ^ (5 : ℕ) * F ^ (2 : ℕ) ≤
        C0 ^ (5 : ℕ) * (2 * (p + L)) :=
      mul_le_mul_of_nonneg_left hF2 (pow_nonneg hC00 5)
    have htail : 0 ≤ gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) := by positivity
    calc
      C0 ^ (5 : ℕ) * F ^ (2 : ℕ) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) =
          (C0 ^ (5 : ℕ) * F ^ (2 : ℕ)) *
            (gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ)) := by ring
      _ ≤ (C0 ^ (5 : ℕ) * (2 * (p + L))) *
            (gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hleft htail
      _ = 2 * C0 ^ (5 : ℕ) * (p + L) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) := by ring
  calc
    C0 * ((C0 * F * G * L ^ (3 : ℕ)) ^ (2 : ℕ) *
          (C0 ^ (2 : ℕ) * L * R ^ (2 : ℕ)) +
        gamma ^ (80 : ℕ) * (C0 ^ (2 : ℕ) * L * R ^ (2 : ℕ))) =
        C0 ^ (5 : ℕ) * F ^ (2 : ℕ) * G ^ (2 : ℕ) * L ^ (7 : ℕ) * R ^ (2 : ℕ) +
          C0 ^ (3 : ℕ) * gamma ^ (80 : ℕ) * L * R ^ (2 : ℕ) := by
            ring
    _ = C0 ^ (5 : ℕ) * F ^ (2 : ℕ) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) +
          C0 ^ (3 : ℕ) * gamma ^ (80 : ℕ) * L * R ^ (2 : ℕ) := by rw [hG2]
    _ ≤ 2 * C0 ^ (5 : ℕ) * (p + L) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) +
          C0 ^ (5 : ℕ) * (p + L) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) :=
      add_le_add hmain hrough
    _ = (3 * C0 ^ (5 : ℕ)) * (p + L) * gamma * L ^ (7 : ℕ) * R ^ (2 : ℕ) := by ring

/-! ## The reachable provider -/

/-- The annealed superdiffusive estimates obtained from the separately named quenched and
random-scale components.  The conclusion has the reachable logarithmic powers `4` and `7`.

No small-time premise is built into the assembly: if the process moment supplier uses a
large-time/small-time split, that split is discharged while constructing
`SuperdiffusivityV2Components`. -/
theorem superdiffusivity_v2_of_components
    (d : ℕ) [NeZero d] (cstar : ℝ) (hcstar : 0 < cstar)
    (gammaBase C0 : ℝ) (hgammaBase : 0 < gammaBase) (hC0 : 1 ≤ C0)
    (hcomponents : ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gammaBase →
      ∀ t : ℝ, 0 < t → ∀ p : ℝ, 1 ≤ p →
        p ≤ C0⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) →
        SuperdiffusivityV2Components M cstar t p C0) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ t : ℝ, 0 < t →
      ∀ p : ℝ, 1 ≤ p →
        p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) →
        (∫⁻ omega : FullSample d M.gamma,
            (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
             letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
             ENNReal.ofReal
                |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
                    ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                        ((0 : Vec d) : OnePoint (Vec d)))) -
                  2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2| ^ p)
            ∂(fullSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
              Real.sqrt M.gamma * |Real.log M.gamma| ^ (4 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p ∧
        (∫⁻ omega : FullSample d M.gamma,
            (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
             letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
             ENNReal.ofReal
                (vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
                    ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                        ((0 : Vec d) : OnePoint (Vec d))))) ^ p)
            ∂(fullSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (p + |Real.log M.gamma|) * M.gamma *
              |Real.log M.gamma| ^ (7 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) ^ p := by
  let gamma0 := min gammaBase (1 / 4)
  let C := max (2 * C0 ^ (4 : ℕ)) (3 * C0 ^ (5 : ℕ))
  have hC00 : 0 < C0 := zero_lt_one.trans_le hC0
  have hgamma0 : 0 < gamma0 := lt_min hgammaBase (by norm_num)
  have hCfirst : 2 * C0 ^ (4 : ℕ) ≤ C := le_max_left _ _
  have hCsecond : 3 * C0 ^ (5 : ℕ) ≤ C := le_max_right _ _
  have hCpos : 0 < C := (mul_pos (by norm_num) (pow_pos hC00 _)).trans_le hCfirst
  refine ⟨gamma0, C, hgamma0, hCpos, ?_⟩
  intro M hcs hgamma t ht p hp hrange
  have hgamma4 : M.gamma ≤ 1 / 4 := hgamma.trans (min_le_right _ _)
  have hgamma1 : M.gamma ≤ 1 := by linarith only [hgamma4]
  have hL : 1 ≤ |Real.log M.gamma| :=
    Algsuperdiff.Section5.Support.one_le_abs_log M.shellPrefix.gamma_pos hgamma4
  have hX : 0 ≤ M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) :=
    mul_nonneg (inv_nonneg.mpr M.shellPrefix.gamma_pos.le) (zpow_nonneg (abs_nonneg _) _)
  have hC0C : C0 ≤ C := by
    calc C0 ≤ 2 * C0 ^ (4 : ℕ) := by
          have hC01 : C0 ≤ C0 ^ (4 : ℕ) := by
            calc C0 ≤ C0 * C0 ^ (3 : ℕ) :=
                  le_mul_of_one_le_right hC00.le (one_le_pow₀ hC0)
              _ = C0 ^ (4 : ℕ) := by ring
          exact hC01.trans (le_mul_of_one_le_left (pow_nonneg hC00.le 4) (by norm_num))
      _ ≤ C := hCfirst
  have hrange0 : p ≤ C0⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) := by
    calc p ≤ C⁻¹ * (M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)) := by
          simpa only [mul_assoc] using hrange
      _ ≤ C0⁻¹ * (M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ)) :=
        mul_le_mul_of_nonneg_right ((inv_le_inv₀ hCpos hC00).2 hC0C) hX
      _ = C0⁻¹ * M.gamma⁻¹ * |Real.log M.gamma| ^ (-6 : ℤ) := by ring
  have H := hcomponents M hcs (hgamma.trans (min_le_left _ _)) t ht p hp hrange0
  have hb := annealed_v2_bounds_of_components M hcstar ht hp hC00.le H
  have hF : 1 ≤ Real.sqrt p + Real.sqrt |Real.log M.gamma| := by
    have hsqrtp : 1 ≤ Real.sqrt p := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hp
    exact hsqrtp.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hR : 0 ≤ intrinsicScale M.nu cstar M.gamma t :=
    (intrinsicScale_pos M.nu_pos hcstar M.shellPrefix.gamma_pos ht).le
  have hfirstAmp := first_v2_amplitude_le (C0 := C0)
    (F := Real.sqrt p + Real.sqrt |Real.log M.gamma|) (G := Real.sqrt M.gamma)
    (L := |Real.log M.gamma|) (R := intrinsicScale M.nu cstar M.gamma t)
    hC0 hF (Real.sqrt_nonneg _) hL hR
  have hF2 := sq_sqrt_add_sqrt_abs_log_le_two_mul_add (p := p) (gamma := M.gamma)
    (zero_le_one.trans hp)
  have hsecondAmp := second_v2_amplitude_le (C0 := C0)
    (F := Real.sqrt p + Real.sqrt |Real.log M.gamma|) (G := Real.sqrt M.gamma)
    (gamma := M.gamma) (L := |Real.log M.gamma|)
    (R := intrinsicScale M.nu cstar M.gamma t) (p := p) hC0 hp
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hF2
    (Real.sqrt_nonneg _) (Real.sq_sqrt M.shellPrefix.gamma_pos.le)
    M.shellPrefix.gamma_pos.le hgamma1 hL hR
  have hfirstCoeff :
      (2 * C0 ^ (4 : ℕ)) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (4 : ℕ) *
          intrinsicScale M.nu cstar M.gamma t ^ 2 ≤
        C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
          |Real.log M.gamma| ^ (4 : ℕ) * intrinsicScale M.nu cstar M.gamma t ^ 2 := by
    have htail : 0 ≤ (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
        Real.sqrt M.gamma * |Real.log M.gamma| ^ (4 : ℕ) *
        intrinsicScale M.nu cstar M.gamma t ^ 2 := by positivity
    calc
      (2 * C0 ^ (4 : ℕ)) * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
          Real.sqrt M.gamma * |Real.log M.gamma| ^ (4 : ℕ) *
          intrinsicScale M.nu cstar M.gamma t ^ 2 =
          (2 * C0 ^ (4 : ℕ)) *
            ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
              |Real.log M.gamma| ^ (4 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) := by ring
      _ ≤ C * ((Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
              |Real.log M.gamma| ^ (4 : ℕ) *
              intrinsicScale M.nu cstar M.gamma t ^ 2) :=
        mul_le_mul_of_nonneg_right hCfirst htail
      _ = C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) * Real.sqrt M.gamma *
          |Real.log M.gamma| ^ (4 : ℕ) * intrinsicScale M.nu cstar M.gamma t ^ 2 := by ring
  have hsecondCoeff :
      (3 * C0 ^ (5 : ℕ)) * (p + |Real.log M.gamma|) * M.gamma *
          |Real.log M.gamma| ^ (7 : ℕ) * intrinsicScale M.nu cstar M.gamma t ^ 2 ≤
        C * (p + |Real.log M.gamma|) * M.gamma * |Real.log M.gamma| ^ (7 : ℕ) *
          intrinsicScale M.nu cstar M.gamma t ^ 2 := by
    have htail : 0 ≤ (p + |Real.log M.gamma|) * M.gamma *
        |Real.log M.gamma| ^ (7 : ℕ) * intrinsicScale M.nu cstar M.gamma t ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (add_nonneg (zero_le_one.trans hp) (abs_nonneg _))
            M.shellPrefix.gamma_pos.le)
          (pow_nonneg (abs_nonneg _) 7))
        (sq_nonneg _)
    calc
      (3 * C0 ^ (5 : ℕ)) * (p + |Real.log M.gamma|) * M.gamma *
          |Real.log M.gamma| ^ (7 : ℕ) * intrinsicScale M.nu cstar M.gamma t ^ 2 =
          (3 * C0 ^ (5 : ℕ)) * ((p + |Real.log M.gamma|) * M.gamma *
            |Real.log M.gamma| ^ (7 : ℕ) * intrinsicScale M.nu cstar M.gamma t ^ 2) := by ring
      _ ≤ C * ((p + |Real.log M.gamma|) * M.gamma *
            |Real.log M.gamma| ^ (7 : ℕ) * intrinsicScale M.nu cstar M.gamma t ^ 2) :=
        mul_le_mul_of_nonneg_right hCsecond htail
      _ = C * (p + |Real.log M.gamma|) * M.gamma * |Real.log M.gamma| ^ (7 : ℕ) *
          intrinsicScale M.nu cstar M.gamma t ^ 2 := by ring
  constructor
  · exact hb.1.trans (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
      (hfirstAmp.trans hfirstCoeff)) (zero_le_one.trans hp))
  · exact hb.2.trans (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
      (hsecondAmp.trans hsecondCoeff)) (zero_le_one.trans hp))

end

end Algsuperdiff.Section5.Provider
