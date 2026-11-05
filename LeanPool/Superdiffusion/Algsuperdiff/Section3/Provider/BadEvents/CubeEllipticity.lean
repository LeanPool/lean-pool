/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LiteralMeasurabilityEngine

/-!
# CubeEllipticity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Multiscale ellipticity of the actual cutoff on an arbitrary triadic cube

`Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity` exposes the
measurable Chapter 4 multiscale ellipticity observables of the literal cutoff
`a_r = nu Id + k_r` on the *centered* cube `square_m`.  ABK26's local bad event
`e.Bloc.def` is stated on the off-centre triadic cube `z + square_j` for `z` in
`3^j Z^d`, i.e. on an arbitrary `TriadicCube d` of scale `j`.

The CoarseGraining-only measurability engine used by the centered file
(`Provider/BadEvents/LiteralMeasurabilityEngine.lean`) is already stated for an
arbitrary cube, so this module is the verbatim generalization of the centered
constructions with `originCube d domainScale` replaced by a cube parameter.
Nothing here is new mathematics; it is the carrier the bad-event definitions
need.

## Main definitions

* `cubeLowerEllipticityInvLiteral`, `cubeUpperEllipticityLiteral`: the literal
  `lambda_{s,q}^{-1}(Q; a_r)` and `Lambda_{s,q}(Q; a_r)`.
* `cubeLowerEllipticityInv`, `cubeUpperEllipticity`: the exported observables,
  the literals clamped at `0`.

## Main results

* `measurable_cubeLowerEllipticityInvLiteral`,
  `measurable_cubeUpperEllipticityLiteral`: genuine measurability of the
  literals, from the engine.
* `measurable_cubeLowerEllipticityInv`, `measurable_cubeUpperEllipticity`
* `cubeLowerEllipticityInv_eq_literal`, `cubeUpperEllipticity_eq_literal`: the
  exported observable **is** its literal, at every sample point.
* `cubeLowerEllipticityInv_ae_eq_literal`, `cubeUpperEllipticity_ae_eq_literal`:
  the almost-everywhere shadows, kept for the consumers that state their
  hypotheses that way.
* `cubeLowerEllipticityInvLiteral_originCube`: on the centered cube the literal
  observable **is** the proved centered literal observable.  Pointwise centered
  agreement therefore follows by composing it with the two `_eq_literal`
  theorems; no separate transport facade is needed.

## References

* ABK26, `e.Bloc.def`.
* ABK26, (2.22)--(2.23), the coarse-grained ellipticity constants.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Nonzero dimension, from the paper-wide assumption `2 <= d` stored in the
model. -/
theorem neZero_of_model (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- Literal inverse lower multiscale ellipticity of the actual cutoff field on
an arbitrary triadic cube.  This is not a measurable representative. -/
noncomputable def cubeLowerEllipticityInvLiteral (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    CutoffSample d → ℝ := by
  letI : NeZero d := neZero_of_model M
  exact fun omega =>
    (Ch04.lambdaSqCoeffField Q s q.1
      (Cutoff.coefficientCutoff M.nu cutoffScale omega))⁻¹

/-- Literal upper multiscale ellipticity of the actual cutoff field on an
arbitrary triadic cube.  This is not a measurable representative. -/
noncomputable def cubeUpperEllipticityLiteral (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    CutoffSample d → ℝ := by
  letI : NeZero d := neZero_of_model M
  exact fun omega => Ch04.LambdaSqCoeffField Q s q.1
    (Cutoff.coefficientCutoff M.nu cutoffScale omega)

/-- The general-cube inverse lower multiscale ellipticity **literal** of the
actual cutoff is genuinely measurable. -/
theorem measurable_cubeLowerEllipticityInvLiteral (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) {s : ℝ} (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    Measurable (cubeLowerEllipticityInvLiteral M Q cutoffScale s q) := by
  let : NeZero d := neZero_of_model M
  exact measurable_comp_lambdaSqCoeffField_inv
    (Cutoff.measurable_coefficientCutoff M.nu cutoffScale)
    (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale) Q hs q.1 q.2

/-- The general-cube upper multiscale ellipticity **literal** of the actual
cutoff is genuinely measurable. -/
theorem measurable_cubeUpperEllipticityLiteral (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) {s : ℝ} (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    Measurable (cubeUpperEllipticityLiteral M Q cutoffScale s q) := by
  let : NeZero d := neZero_of_model M
  exact measurable_comp_LambdaSqCoeffField
    (Cutoff.measurable_coefficientCutoff M.nu cutoffScale)
    (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale) Q hs q.1 q.2

private theorem cubeLowerEllipticityInvLiteral_nonneg (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) {s : ℝ} (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    0 ≤ cubeLowerEllipticityInvLiteral M Q cutoffScale s q omega := by
  let : NeZero d := neZero_of_model M
  unfold cubeLowerEllipticityInvLiteral
  exact inv_nonneg.mpr <| by
    rw [Ch04.lambdaSqCoeffField]
    simp only [dite_eq_left
      (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale omega)]
    exact Ch02.lambdaSq_nonneg Q
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (Cutoff.coefficientCutoff M.nu cutoffScale omega)
        (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale
          omega)) hs q.2

private theorem cubeUpperEllipticityLiteral_nonneg (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) {s : ℝ} (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    0 ≤ cubeUpperEllipticityLiteral M Q cutoffScale s q omega := by
  let : NeZero d := neZero_of_model M
  unfold cubeUpperEllipticityLiteral
  rw [Ch04.LambdaSqCoeffField]
  simp only [dite_eq_left
    (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale omega)]
  exact Ch02.LambdaSq_nonneg Q
    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (Cutoff.coefficientCutoff M.nu cutoffScale omega)
      (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale
        omega)) hs q.2

/-- The actual `lambda_{s,q}^{-1}(Q; a_r)` on an arbitrary triadic cube: the
literal, clamped at `0`. -/
noncomputable def cubeLowerEllipticityInv (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (_hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    CutoffSample d → ℝ :=
  fun omega => max 0 (cubeLowerEllipticityInvLiteral M Q cutoffScale s q omega)

/-- The actual `Lambda_{s,q}(Q; a_r)` on an arbitrary triadic cube: the literal,
clamped at `0`. -/
noncomputable def cubeUpperEllipticity (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (_hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    CutoffSample d → ℝ :=
  fun omega => max 0 (cubeUpperEllipticityLiteral M Q cutoffScale s q omega)

theorem measurable_cubeLowerEllipticityInv (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    Measurable (cubeLowerEllipticityInv M Q cutoffScale s hs q) :=
  measurable_const.max (measurable_cubeLowerEllipticityInvLiteral M Q cutoffScale hs q)

theorem measurable_cubeUpperEllipticity (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    Measurable (cubeUpperEllipticity M Q cutoffScale s hs q) :=
  measurable_const.max (measurable_cubeUpperEllipticityLiteral M Q cutoffScale hs q)

theorem cubeLowerEllipticityInv_nonneg (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    0 ≤ cubeLowerEllipticityInv M Q cutoffScale s hs q omega :=
  le_max_left _ _

/-- **The exported general-cube inverse lower observable is its literal**, at
every sample point.  The clamp is inert on the source range `0 < s`. -/
theorem cubeLowerEllipticityInv_eq_literal (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    cubeLowerEllipticityInv M Q cutoffScale s hs q =
      cubeLowerEllipticityInvLiteral M Q cutoffScale s q := by
  funext omega
  exact max_eq_right (cubeLowerEllipticityInvLiteral_nonneg M Q cutoffScale hs q omega)

/-- **The exported general-cube upper observable is its literal**, at every
sample point. -/
theorem cubeUpperEllipticity_eq_literal (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    cubeUpperEllipticity M Q cutoffScale s hs q =
      cubeUpperEllipticityLiteral M Q cutoffScale s q := by
  funext omega
  exact max_eq_right (cubeUpperEllipticityLiteral_nonneg M Q cutoffScale hs q omega)

theorem cubeLowerEllipticityInv_ae_eq_literal (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    cubeLowerEllipticityInv M Q cutoffScale s hs q
        =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      cubeLowerEllipticityInvLiteral M Q cutoffScale s q :=
  (cubeLowerEllipticityInv_eq_literal M Q cutoffScale s hs q) ▸ Filter.EventuallyEq.rfl

theorem cubeUpperEllipticity_ae_eq_literal (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    cubeUpperEllipticity M Q cutoffScale s hs q
        =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      cubeUpperEllipticityLiteral M Q cutoffScale s q :=
  (cubeUpperEllipticity_eq_literal M Q cutoffScale s hs q) ▸ Filter.EventuallyEq.rfl

/-- On the centered cube the literal observable is the proved centered literal
observable. -/
theorem cubeLowerEllipticityInvLiteral_originCube (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent) :
    cubeLowerEllipticityInvLiteral M (originCube d domainScale) cutoffScale s q =
      Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInvLiteral M
        domainScale cutoffScale s q :=
  rfl

end

end Algsuperdiff.Section3.Provider.BadEvents
