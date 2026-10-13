/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.Definitions
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.TranslationCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ToLambdasUpper
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError

/-!
# CenteredIdentification

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# From the local bad event to the centered homogenization error

Step 1 of the proof of ABK26's `l.bad.event.probabilities` reads: by
`e.bound.Lambdas.by.Es`, on `B_loc(z + square_j)` the multiscale homogenization
error at that cube is larger than a constant; the induction hypothesis
`e.new.induction.for.shom` then bounds the probability.

This module proves a local version of the first half of that sentence and moves the resulting
event to the *centered* cube where the induction state lives.

## The two links

* `one_lt_cubeHomogenizationErrorLiteral_of_mem_badLoc`.  The proved sharp two-sided
  comparison
  `ErrorComparison.max_weightedEllipticity_le_one_add_two_mul_sq_add_sqrt_two_mul` gives
  `max{sigma^{-1} Lambda_{1/4,2}, sigma lambda_{1/4,2}^{-1}} <= 1 + 2 E^2 + 2^{1/2} E`. On
  `B_loc` the left side exceeds `10`, while at `E <= 1` the right side is at most `1 + 2 +
  2 = 5 < 10`. Hence `E > 1` on `B_loc`. (The manuscript's unspecified threshold constant
  `C` is chosen here as `1`; the honest root of `2x^2 + 2^{1/2} x = 9` is `1.797...`.)
* `badLoc_ae_le_preimage`.  Combining with the deterministic covariance of
  `TranslationCovariance.lean` and the translation invariance of the cutoff
  sample law, the event `B_loc(z + square_j)` is almost surely contained in the
  translate of the *centered* upper-tail event
  `{ E_{1/4,infinity,2}(square_j; a_j, sigma_j) > 1 }`, whose probability is
  what the induction state controls.

## Main results

* `cubeHomogenizationErrorLiteral`
* `one_lt_cubeHomogenizationErrorLiteral_of_mem_badLoc`
* `badLoc_ae_le_preimage`
* `measureReal_badLoc_le_measureReal_centeredTail`

## References

* ABK26, `l.bad.event.probabilities`, Step 1.
* ABK26, `e.bound.Lambdas.by.Es`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Nonzero dimension, from the paper-wide assumption `2 <= d` stored in the
model. -/
theorem neZeroOfModel (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The exponent `s = 1/4` of `e.Bloc.def`, in the positivity subtype used by
the induction state `d.mathcalS.def`. -/
def quarter : {s : ℝ // 0 < s} := ⟨1 / 4, by norm_num⟩

/-! ## The literal multiscale homogenization error at an arbitrary cube -/

/-- The literal `mathcal E_{1/4,infinity,2}(Q; a_{Q.scale}, sigma_{Q.scale} Id)` of
the actual coefficient cutoff at an arbitrary triadic cube.  On the centered
cube it is almost surely the proved observable
`Observable.cutoffHomogenizationError`. -/
def cubeHomogenizationErrorLiteral [NeZero d] (M : ABKModel d) (Q : TriadicCube d)
    (omega : CutoffSample d) : ℝ :=
  Ch02.HomogenizationErrorOnCube Q (1 / 4) .infinity (.finite 2)
    (coefficientCutoffTriadicCoeffFamily M Q.scale omega)
    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M Q.scale))

/-! ## The two literal ellipticity observables as Chapter 2 quantities -/

/-- The literal inverse lower ellipticity of the cutoff is the Chapter 2
quantity of the canonical Chapter 4 coefficient family. -/
theorem cubeLowerEllipticityInvLiteral_eq [NeZero d] (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) (omega : CutoffSample d) :
    cubeLowerEllipticityInvLiteral M Q cutoffScale s q omega =
      (Ch02.lambdaSq Q s q.1
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (coefficientCutoff M.nu cutoffScale omega)
          (coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale
            omega)))⁻¹ := by
  unfold cubeLowerEllipticityInvLiteral
  congr 1
  rw [Ch04.lambdaSqCoeffField]
  simp only [dite_eq_left
    (coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale omega)]

/-- The literal upper ellipticity of the cutoff is the Chapter 2 quantity of the
canonical Chapter 4 coefficient family. -/
theorem cubeUpperEllipticityLiteral_eq [NeZero d] (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) (omega : CutoffSample d) :
    cubeUpperEllipticityLiteral M Q cutoffScale s q omega =
      Ch02.LambdaSq Q s q.1
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (coefficientCutoff M.nu cutoffScale omega)
          (coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale
            omega)) := by
  unfold cubeUpperEllipticityLiteral
  rw [Ch04.LambdaSqCoeffField]
  simp only [dite_eq_left
    (coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale omega)]

/-! ## Step 1 of the manuscript's proof -/

/-- `sqrt 2 <= 2`, the only numerical input of the threshold comparison. -/
private theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  calc Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    _ = 2 := h4

/-- **Step 1 of `l.bad.event.probabilities`.**  At any sample where the two
measurable ellipticity representatives take their literal values, membership in
`B_loc(z + square_j)` forces the multiscale homogenization error at that cube
to exceed `1`.

The manuscript's display is `P[B_loc] <= P[E^2 > C]`; the chosen threshold is
the explicit `E > 1`, which is below the honest root `1.797...` of
`2x^2 + 2^{1/2} x = 9`. -/
theorem one_lt_cubeHomogenizationErrorLiteral_of_mem_badLoc [NeZero d]
    (M : ABKModel d) (Q : TriadicCube d) {omega : CutoffSample d}
    (hlow : cubeLowerEllipticityInv M Q Q.scale (1 / 4) (by norm_num) exponentTwo
        omega =
      cubeLowerEllipticityInvLiteral M Q Q.scale (1 / 4) exponentTwo omega)
    (hup : cubeUpperEllipticity M Q Q.scale (1 / 4) (by norm_num) exponentTwo
        omega =
      cubeUpperEllipticityLiteral M Q Q.scale (1 / 4) exponentTwo omega)
    (hmem : omega ∈ badLoc M Q) :
    1 < cubeHomogenizationErrorLiteral M Q omega := by
  set sigma : Algsuperdiff.Section3.Observable.PositiveScalar :=
    Annealed.sigmaBar M Q.scale with hsigma
  have hpos : (0 : ℝ) < (sigma : ℝ) := sigma.2
  set F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (coefficientCutoff M.nu Q.scale omega)
      (coefficientCutoff_aeLocallyUniformlyEllipticField M Q.scale omega) with hF
  set Elit : ℝ := Ch02.HomogenizationErrorOnCube Q (1 / 4) .infinity (.finite 2) F
    (scalarMatrix (d := d) (sigma : ℝ)) with hElit
  have hEeq : cubeHomogenizationErrorLiteral M Q omega = Elit := by
    rw [hElit, hF, cubeHomogenizationErrorLiteral]
    exact (Ch02.HomogenizationErrorOnCube_eq_ofAEEq
      (coefficientCutoff_canonicalFamily_aeeq M Q.scale omega) Q (1 / 4) .infinity
      (.finite 2) (scalarMatrix (d := d) (sigma : ℝ))).symm
  have hnn : 0 ≤ Elit :=
    ErrorComparison.homogenizationErrorOnCube_infinity_two_nonneg Q F
      (scalarMatrix (d := d) (sigma : ℝ)) (by norm_num : (0 : ℝ) < 1 / 4)
  have hcmp :
      max ((sigma : ℝ)⁻¹ * Ch02.LambdaSq Q (1 / 4) (.finite 2) F)
          ((sigma : ℝ) * (Ch02.lambdaSq Q (1 / 4) (.finite 2) F)⁻¹) ≤
        1 + 2 * Elit ^ 2 + Real.sqrt 2 * Elit :=
    ErrorComparison.max_weightedEllipticity_le_one_add_two_mul_sq_add_sqrt_two_mul
      Q F (by norm_num : (0 : ℝ) < 1 / 4) hpos
  have h10 : (10 : ℝ) <
      max ((sigma : ℝ)⁻¹ * Ch02.LambdaSq Q (1 / 4) (.finite 2) F)
        ((sigma : ℝ) * (Ch02.lambdaSq Q (1 / 4) (.finite 2) F)⁻¹) := by
    rcases hmem with hmem | hmem
    · have hmem' : 10 * (sigma : ℝ)⁻¹ <
          (Ch02.lambdaSq Q (1 / 4) (.finite 2) F)⁻¹ := by
        have h : 10 * (sigma : ℝ)⁻¹ <
            cubeLowerEllipticityInvLiteral M Q Q.scale (1 / 4) exponentTwo omega :=
          lt_of_lt_of_eq hmem hlow
        rw [cubeLowerEllipticityInvLiteral_eq] at h
        exact h
      have hscaled := mul_lt_mul_of_pos_left hmem' hpos
      have hcancel : (sigma : ℝ) * (10 * (sigma : ℝ)⁻¹) = 10 := by
        field_simp
      rw [hcancel] at hscaled
      exact lt_of_lt_of_le hscaled (le_max_right _ _)
    · have hmem' : 10 * (sigma : ℝ) < Ch02.LambdaSq Q (1 / 4) (.finite 2) F := by
        have h : 10 * (sigma : ℝ) <
            cubeUpperEllipticityLiteral M Q Q.scale (1 / 4) exponentTwo omega :=
          lt_of_lt_of_eq hmem hup
        rw [cubeUpperEllipticityLiteral_eq] at h
        exact h
      have hinv : (0 : ℝ) < (sigma : ℝ)⁻¹ := inv_pos.2 hpos
      have hscaled := mul_lt_mul_of_pos_left hmem' hinv
      have hcancel : (sigma : ℝ)⁻¹ * (10 * (sigma : ℝ)) = 10 := by
        field_simp
      rw [hcancel] at hscaled
      exact lt_of_lt_of_le hscaled (le_max_left _ _)
  rw [hEeq]
  by_contra hcon
  push Not at hcon
  have hchain : (10 : ℝ) < 1 + 2 * Elit ^ 2 + Real.sqrt 2 * Elit :=
    lt_of_lt_of_le h10 hcmp
  have hsq : Elit ^ 2 ≤ 1 := by nlinarith
  have hlin : Real.sqrt 2 * Elit ≤ 2 := by
    nlinarith [sqrt_two_le_two, Real.sqrt_nonneg 2]
  linarith

/-! ## Transport to the centered cube -/

/-- **Step 1 local event identification.**  The local bad event at `z + square_j` is almost
surely contained in the `translateCutoffSample`-preimage of the centered
upper-tail event `{ E_{1/4,infinity,2}(square_j; a_j, sigma_j) > 1 }`.

The deterministic content is `homogenizationErrorOnCube_translateCutoffSample`;
the null sets discarded are the two ellipticity-representative sets and the
representative set of the centered observable, pulled back along the
measure-preserving translation. -/
theorem badLoc_ae_le_preimage (M : ABKModel d) (Q : TriadicCube d) :
    badLoc M Q ≤ᵐ[(cutoffSampleLaw M).toMeasure]
      (translateCutoffSample (triadicCubeShift Q)) ⁻¹'
        {omega | 1 < Observable.cutoffHomogenizationError M Q.scale quarter omega} := by
  let : NeZero d := neZeroOfModel M
  have hlow := cubeLowerEllipticityInv_ae_eq_literal M Q Q.scale (1 / 4)
    (by norm_num) exponentTwo
  have hup := cubeUpperEllipticity_ae_eq_literal M Q Q.scale (1 / 4)
    (by norm_num) exponentTwo
  have hbase : Observable.cutoffHomogenizationError M Q.scale quarter
      =ᵐ[(cutoffSampleLaw M).toMeasure]
      fun w => Ch02.HomogenizationErrorOnCube (originCube d Q.scale)
        ((quarter : ℝ)) .infinity (.finite 2)
        (coefficientCutoffTriadicCoeffFamily M Q.scale w)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M Q.scale)) :=
    Observable.cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube M Q.scale
      quarter
  have hcen : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Observable.cutoffHomogenizationError M Q.scale quarter
          (translateCutoffSample (triadicCubeShift Q) omega) =
        Ch02.HomogenizationErrorOnCube (originCube d Q.scale) ((quarter : ℝ))
          .infinity (.finite 2)
          (coefficientCutoffTriadicCoeffFamily M Q.scale
            (translateCutoffSample (triadicCubeShift Q) omega))
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M Q.scale)) := by
    refine MeasureTheory.ae_of_ae_map
      (p := fun w => Observable.cutoffHomogenizationError M Q.scale quarter w =
        Ch02.HomogenizationErrorOnCube (originCube d Q.scale) ((quarter : ℝ))
          .infinity (.finite 2)
          (coefficientCutoffTriadicCoeffFamily M Q.scale w)
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M Q.scale)))
      (measurable_translateCutoffSample (triadicCubeShift Q)).aemeasurable ?_
    rw [map_translateCutoffSample_cutoffSampleLaw]
    exact hbase
  filter_upwards [hlow, hup, hcen] with omega h1 h2 h3 hmem
  have hcov := homogenizationErrorOnCube_translateCutoffSample M Q.scale Q
    ((quarter : ℝ)) Ch02.MultiscaleExponent.infinity
    (Ch02.MultiscaleExponent.finite 2)
    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M Q.scale)) omega
  show 1 < Observable.cutoffHomogenizationError M Q.scale quarter
    (translateCutoffSample (triadicCubeShift Q) omega)
  rw [h3, ← hcov]
  exact one_lt_cubeHomogenizationErrorLiteral_of_mem_badLoc M Q h1 h2 hmem

/-- The probability of the local bad event at `z + square_j` is bounded by the
probability of the centered upper-tail event, by translation invariance of the
cutoff sample law. -/
theorem measureReal_badLoc_le_measureReal_centeredTail (M : ABKModel d)
    (Q : TriadicCube d) :
    (cutoffSampleLaw M).toMeasure.real (badLoc M Q) ≤
      (cutoffSampleLaw M).toMeasure.real
        {omega | 1 < Observable.cutoffHomogenizationError M Q.scale quarter omega} := by
  set mu := (cutoffSampleLaw M).toMeasure with hmu
  set S : Set (CutoffSample d) :=
    {omega | 1 < Observable.cutoffHomogenizationError M Q.scale quarter omega} with hS
  have hSmeas : MeasurableSet S :=
    measurableSet_lt measurable_const
      (Observable.measurable_cutoffHomogenizationError M Q.scale quarter)
  have hpre : mu ((translateCutoffSample (triadicCubeShift Q)) ⁻¹' S) = mu S := by
    rw [← MeasureTheory.Measure.map_apply
      (measurable_translateCutoffSample (triadicCubeShift Q)) hSmeas,
      hmu, map_translateCutoffSample_cutoffSampleLaw]
  have hmono : mu (badLoc M Q) ≤ mu ((translateCutoffSample (triadicCubeShift Q)) ⁻¹' S) :=
    measure_mono_ae (badLoc_ae_le_preimage M Q)
  have hle : mu (badLoc M Q) ≤ mu S := by rw [← hpre]; exact hmono
  exact ENNReal.toReal_mono (measure_ne_top mu S) hle

end

end Algsuperdiff.Section3.Provider.BadEvents
