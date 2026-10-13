/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMomentsCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.SuperdiffusiveBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.RemovalSteps
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.StreamProcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.RenormalizationAtRandomScale
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ParameterizedProcessSemigroup

/-!
# QuenchedMomentsComposer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Quenched displacement-moment composition

This module combines the stopped cube estimates, stopping-time removal, and
the comparison of the running diffusivity with the intrinsic scale.  The
process-moment and cube-moment inputs are kept as separately named hypotheses
in the forms delivered by their respective provider layers.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form HCPolySupport MarkovProcess MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The quenched second-moment comparison obtained by summing the directional
stopped estimates and combining them with stopping-time removal and the
intrinsic-scale comparison. -/
theorem secondMoment_quenched_of_moments (M : ABKModel d) (cstar t C0 : ℝ)
    (omega : FullSample d M.gamma)
    (S EB : ℤ → Cutoff.CutoffSample d → ℝ) (L : ℝ)
    (c : Vec d → ℝ) (sigmaBar exitProbability Ccube Cremove Cscale : ℝ)
    (ht : 0 < t)
    (hgamma4 : M.gamma ≤ 1 / 4)
    (hCremove : 0 ≤ Cremove)
    (hEBnn : ∀ n eta, 0 ≤ EB n eta)
    (hexitProbability : 0 ≤ exitProbability)
    (hscaleSq : 0 ≤ ((3 : ℝ) ^
      (confinementScale S L omega.1)) ^ (2 : ℕ))
    (hsigmaTime_le : (d : ℝ) * (sigmaBar * t) ≤
      ((3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ))
    (hC3 : letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      ∀ i : Fin d,
        |(∫ path, onePointRealExtension
              (fun z => c z * quadraticObservable (basisVec i) z)
              (path (ContinuousPath.exitTimeTrunc
                (((↑) : Vec d → OnePoint (Vec d)) ''
                  cubeSetAt (0 : Vec d) (confinementScale S L omega.1))
                t.toNNReal path))
          ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
              ((0 : Vec d) : OnePoint (Vec d)))) -
            (2 * sigmaBar) * (t.toNNReal : ℝ)| ≤
          Ccube * ((3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ) *
              EB (confinementScale S L omega.1) omega.1 +
            2 * (sigmaBar * (t.toNNReal : ℝ)) * exitProbability)
    (hQmeas : ∀ i : Fin d,
      Measurable fun z => c z * quadraticObservable (basisVec i) z)
    {CQ : ℝ} (hCQ : ∀ (i : Fin d) (z : Vec d),
      |c z * quadraticObservable (basisVec i) z| ≤ CQ)
    (hC6 : letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      abs ((∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
          ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
              ((0 : Vec d) : OnePoint (Vec d)))) -
        (∫ path, onePointRealExtension (fun z => c z * vecNormSq z)
            (path (ContinuousPath.exitTimeTrunc
              (((↑) : Vec d → OnePoint (Vec d)) ''
                cubeSetAt (0 : Vec d) (confinementScale S L omega.1))
              t.toNNReal path))
          ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
              ((0 : Vec d) : OnePoint (Vec d))))) ≤
        Cremove * M.gamma ^ (50 : ℕ) *
          ((3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ))
    (hprofile : |(d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2 -
        (d : ℝ) * (sigmaBar * t)| ≤
      Cscale * Real.sqrt M.gamma * |Real.log M.gamma| *
        ((3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ))
    (hearlyExit : exitProbability ≤ M.gamma ^ (100 : ℕ))
    (hCstopped : (d : ℝ) * Ccube ≤ C0)
    (hCtail : Cremove + 2 + 2 * Cscale ≤ C0) :
    (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
     letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
     |(∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
          ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
              ((0 : Vec d) : OnePoint (Vec d)))) -
        2 * (d : ℝ) * intrinsicScale M.nu cstar M.gamma t ^ 2|) ≤
      C0 * (EB (confinementScale S L omega.1) omega.1 +
        Real.sqrt M.gamma * |Real.log M.gamma|) *
          ((3 : ℝ) ^ (confinementScale S L omega.1)) ^ 2 := by
  let input := streamExhaustionTailInput M omega
  let instMetric : MetricSpace (OnePoint (Vec d)) := input.toOnePointRegular.metricSpace
  let instComplete : CompleteSpace (OnePoint (Vec d)) :=
    input.toOnePointRegular.completeSpace
  let m := confinementScale S L omega.1
  let scaleSq : ℝ := ((3 : ℝ) ^ m) ^ (2 : ℕ)
  let err : ℝ := EB m omega.1
  let stoppedSecondMoment : ℝ :=
    ∫ path, onePointRealExtension (fun z => c z * vecNormSq z)
        (path (ContinuousPath.exitTimeTrunc
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m)
          t.toNNReal path))
      ∂input.wholeSpaceProcess ((0 : Vec d) : OnePoint (Vec d))
  let fullSecondMoment : ℝ :=
    ∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
      ∂input.wholeSpaceProcess ((0 : Vec d) : OnePoint (Vec d))
  have htNN : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht.le
  have hC3' : ∀ i : Fin d,
      |(∫ path, onePointRealExtension
            (fun z => c z * quadraticObservable (basisVec i) z)
            (path (ContinuousPath.exitTimeTrunc
              (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m)
              t.toNNReal path))
          ∂input.wholeSpaceProcess ((0 : Vec d) : OnePoint (Vec d))) -
        (2 * sigmaBar) * (t.toNNReal : ℝ)| ≤
        Ccube * scaleSq * err +
          2 * (sigmaBar * (t.toNNReal : ℝ)) * exitProbability := by
    simpa only [m, input, scaleSq, err] using hC3
  have hstopped : |stoppedSecondMoment - 2 * ((d : ℝ) * (sigmaBar * t))| ≤
      ((d : ℝ) * Ccube) * scaleSq * err +
        2 * ((d : ℝ) * (sigmaBar * t)) * exitProbability := by
    have hsum := abs_integral_eval_exitTimeTrunc_vecNormSq_sub_le_cubeSetAt
      (streamWholeSpaceResolvent M omega) input.toOnePointRegular 0 m hQmeas hCQ t.toNNReal hC3'
    dsimp only [stoppedSecondMoment, input, m, scaleSq, err]
    calc
      |(∫ path, onePointRealExtension (fun z => c z * vecNormSq z)
            (path (ContinuousPath.exitTimeTrunc
              (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m)
              t.toNNReal path))
          ∂(streamExhaustionTailInput M omega).wholeSpaceProcess
              ((0 : Vec d) : OnePoint (Vec d))) -
          2 * ((d : ℝ) * (sigmaBar * t))| =
          |(∫ path, onePointRealExtension (fun z => c z * vecNormSq z)
              (path (ContinuousPath.exitTimeTrunc
                (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m)
                t.toNNReal path))
            ∂(streamExhaustionTailInput M omega).wholeSpaceProcess
                ((0 : Vec d) : OnePoint (Vec d))) -
            (d : ℝ) * (2 * sigmaBar * t)| := by congr 1; ring
      _ ≤ (d : ℝ) * (Ccube * ((3 : ℝ) ^ m) ^ (2 : ℕ) * EB m omega.1 +
            2 * (sigmaBar * t) * exitProbability) := by
        simp only [htNN] at hsum
        exact hsum
      _ = ((d : ℝ) * Ccube) * ((3 : ℝ) ^ m) ^ (2 : ℕ) * EB m omega.1 +
            2 * ((d : ℝ) * (sigmaBar * t)) * exitProbability := by ring
  have hraw := abs_fullSecondMoment_sub_two_mul_intrinsicSq_le_of_components
    M.shellPrefix.gamma_pos hgamma4 hscaleSq hsigmaTime_le hCremove hexitProbability
    hstopped hC6 hprofile hearlyExit
  have herr : 0 ≤ err := by
    dsimp only [err, m]
    exact hEBnn _ _
  have hA : 0 ≤ Real.sqrt M.gamma * |Real.log M.gamma| :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hcoeff : (d : ℝ) * Ccube * err +
      (Cremove + 2 + 2 * Cscale) *
        (Real.sqrt M.gamma * |Real.log M.gamma|) ≤
      C0 * (err + Real.sqrt M.gamma * |Real.log M.gamma|) := by
    calc
      (d : ℝ) * Ccube * err + (Cremove + 2 + 2 * Cscale) *
          (Real.sqrt M.gamma * |Real.log M.gamma|) ≤
          C0 * err + C0 * (Real.sqrt M.gamma * |Real.log M.gamma|) :=
        add_le_add (mul_le_mul_of_nonneg_right hCstopped herr)
          (mul_le_mul_of_nonneg_right hCtail hA)
      _ = C0 * (err + Real.sqrt M.gamma * |Real.log M.gamma|) := by ring
  have hfinal := hraw.trans (mul_le_mul_of_nonneg_right hcoeff hscaleSq)
  dsimp only [fullSecondMoment, input, err, scaleSq, m] at hfinal ⊢
  rw [mul_assoc (2 : ℝ) (d : ℝ)]
  exact hfinal

/-- The quenched squared-mean comparison obtained from the stopped mean and
the squared stopping-time-removal estimate. -/
theorem meanSq_quenched_of_moments (M : ABKModel d) (t C0 : ℝ)
    (omega : FullSample d M.gamma)
    (S EB : ℤ → Cutoff.CutoffSample d → ℝ) (L : ℝ)
    (stoppedMean : Vec d) (Cstopped Cremove : ℝ)
    (hgamma4 : M.gamma ≤ 1 / 4)
    (hscaleSq : 0 ≤ ((3 : ℝ) ^
      (confinementScale S L omega.1)) ^ (2 : ℕ))
    (hCremove : 0 ≤ Cremove)
    (hC5 : vecNormSq stoppedMean ≤
      Cstopped * ((3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ) *
        EB (confinementScale S L omega.1) omega.1 ^ (2 : ℕ))
    (hC4 : letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
      letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
      vecNormSq
        ((∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
            ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                ((0 : Vec d) : OnePoint (Vec d)))) - stoppedMean) ≤
          Cremove * M.gamma ^ (100 : ℕ) *
            ((3 : ℝ) ^ (confinementScale S L omega.1)) ^ (2 : ℕ))
    (hCstopped : 2 * Cstopped ≤ C0) (hCtail : 2 * Cremove ≤ C0) :
    (letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
     letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
     vecNormSq (∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
          ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
              ((0 : Vec d) : OnePoint (Vec d))))) ≤
      C0 * (EB (confinementScale S L omega.1) omega.1 ^ 2 +
        M.gamma ^ (80 : ℕ)) *
          ((3 : ℝ) ^ (confinementScale S L omega.1)) ^ 2 := by
  let input := streamExhaustionTailInput M omega
  let instMetric : MetricSpace (OnePoint (Vec d)) := input.toOnePointRegular.metricSpace
  let instComplete : CompleteSpace (OnePoint (Vec d)) :=
    input.toOnePointRegular.completeSpace
  let m := confinementScale S L omega.1
  let scaleSq : ℝ := ((3 : ℝ) ^ m) ^ (2 : ℕ)
  let err : ℝ := EB m omega.1
  let fullMean : Vec d :=
    ∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
      ∂input.wholeSpaceProcess ((0 : Vec d) : OnePoint (Vec d))
  have hraw := vecNormSq_fullMean_le_of_stopped_and_removal
    M.shellPrefix.gamma_pos hgamma4 hscaleSq hCremove hC5 hC4
  have herrSq : 0 ≤ err ^ (2 : ℕ) := sq_nonneg err
  have hgammaPow : 0 ≤ M.gamma ^ (80 : ℕ) := pow_nonneg M.shellPrefix.gamma_pos.le _
  have hcoeff : 2 * Cstopped * err ^ (2 : ℕ) +
      2 * Cremove * M.gamma ^ (80 : ℕ) ≤
      C0 * (err ^ (2 : ℕ) + M.gamma ^ (80 : ℕ)) := by
    calc
      2 * Cstopped * err ^ (2 : ℕ) + 2 * Cremove * M.gamma ^ (80 : ℕ) ≤
          C0 * err ^ (2 : ℕ) + C0 * M.gamma ^ (80 : ℕ) :=
        add_le_add (mul_le_mul_of_nonneg_right hCstopped herrSq)
          (mul_le_mul_of_nonneg_right hCtail hgammaPow)
      _ = C0 * (err ^ (2 : ℕ) + M.gamma ^ (80 : ℕ)) := by ring
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff hscaleSq)

end

end Algsuperdiff.Section5.Provider
