/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LawCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Exponent
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LiteralMeasurabilityEngine

/-!
# CutoffMultiscaleEllipticity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Measurable multiscale ellipticity of the actual cutoff

The raw quantities below are the Chapter 4 canonical coefficient-family
observables of the literal cutoff `a_r = nu Id + k_r`.  On the source range
`0 < s`, the exported functions are the literal observables clamped at `0`;
they are genuinely measurable, and they agree with the literals everywhere on
the source range, not merely almost everywhere.  The positivity proof is a
well-definedness input, not a probabilistic or analytic hypothesis: every
Section 3 source window already entails it.

## Main definitions

* `cutoffLowerEllipticityInvLiteral`, `cutoffUpperEllipticityLiteral`: the
  literal Chapter 4 endpoints at the centered cube.
* `cutoffLowerEllipticityInv`, `cutoffUpperEllipticity`: the exported
  observables, the literals clamped at `0`.

## Main results

* `measurable_cutoffLowerEllipticityInvLiteral`,
  `measurable_cutoffUpperEllipticityLiteral`: genuine measurability of the
  literals, from the engine.
* `measurable_cutoffLowerEllipticityInv`, `measurable_cutoffUpperEllipticity`.
* `cutoffLowerEllipticityInv_nonneg`, `cutoffUpperEllipticity_nonneg`.
* `cutoffLowerEllipticityInv_eq_literal`, `cutoffUpperEllipticity_eq_literal`:
  the exported observable **is** its literal, at every sample point.
* `cutoffLowerEllipticityInv_ae_eq_literal`, `cutoffUpperEllipticity_ae_eq_literal`:
  the almost-everywhere shadows, kept for the consumers that state their
  hypotheses that way.
-/

namespace Algsuperdiff.Section3.Observable

open Filter MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

theorem neZero_of_model_CutoffMultiscaleEllipticity (M : ABKModel d) : NeZero d := by
  constructor
  exact Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)

/-- Literal inverse lower multiscale ellipticity of the actual cutoff field.
This is not selected as a measurable representative. -/
noncomputable def cutoffLowerEllipticityInvLiteral (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ)
    (q : CoarseEllipticityExponent) : CutoffSample d → ℝ := by
  letI : NeZero d := neZero_of_model_CutoffMultiscaleEllipticity M
  exact fun omega =>
    (Ch04.lambdaSqCoeffField (originCube d domainScale) s q.1
      (Cutoff.coefficientCutoff M.nu cutoffScale omega))⁻¹

/-- Literal upper multiscale ellipticity of the actual cutoff field.  This is
not selected as a measurable representative. -/
noncomputable def cutoffUpperEllipticityLiteral (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ)
    (q : CoarseEllipticityExponent) : CutoffSample d → ℝ := by
  letI : NeZero d := neZero_of_model_CutoffMultiscaleEllipticity M
  exact fun omega => Ch04.LambdaSqCoeffField (originCube d domainScale) s q.1
    (Cutoff.coefficientCutoff M.nu cutoffScale omega)

/-- **Genuine** measurability of the centered inverse lower multiscale
ellipticity literal, from the carrier-source engine at the centered cube. -/
theorem measurable_cutoffLowerEllipticityInvLiteral (M : ABKModel d)
    (domainScale cutoffScale : ℤ) {s : ℝ} (hs : 0 < s)
    (q : CoarseEllipticityExponent) :
    Measurable (cutoffLowerEllipticityInvLiteral M domainScale cutoffScale s q) := by
  let : NeZero d := neZero_of_model_CutoffMultiscaleEllipticity M
  exact Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_lambdaSqCoeffField_inv
    (Cutoff.measurable_coefficientCutoff M.nu cutoffScale)
    (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale)
    (originCube d domainScale) hs q.1 q.2

/-- **Genuine** measurability of the centered upper multiscale ellipticity
literal, from the carrier-source engine at the centered cube. -/
theorem measurable_cutoffUpperEllipticityLiteral (M : ABKModel d)
    (domainScale cutoffScale : ℤ) {s : ℝ} (hs : 0 < s)
    (q : CoarseEllipticityExponent) :
    Measurable (cutoffUpperEllipticityLiteral M domainScale cutoffScale s q) := by
  let : NeZero d := neZero_of_model_CutoffMultiscaleEllipticity M
  exact Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_LambdaSqCoeffField
    (Cutoff.measurable_coefficientCutoff M.nu cutoffScale)
    (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale)
    (originCube d domainScale) hs q.1 q.2

private theorem cutoffLowerEllipticityInvLiteral_nonneg (M : ABKModel d)
    (domainScale cutoffScale : ℤ) {s : ℝ} (hs : 0 < s)
    (q : CoarseEllipticityExponent) (omega : CutoffSample d) :
    0 ≤ cutoffLowerEllipticityInvLiteral M domainScale cutoffScale s q omega := by
  let : NeZero d := neZero_of_model_CutoffMultiscaleEllipticity M
  unfold cutoffLowerEllipticityInvLiteral
  exact inv_nonneg.mpr <| by
    rw [Ch04.lambdaSqCoeffField]
    simp only [dite_eq_left (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M
      cutoffScale omega)]
    exact Ch02.lambdaSq_nonneg (originCube d domainScale)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (Cutoff.coefficientCutoff M.nu cutoffScale omega)
        (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale omega)) hs q.2

private theorem cutoffUpperEllipticityLiteral_nonneg (M : ABKModel d)
    (domainScale cutoffScale : ℤ) {s : ℝ} (hs : 0 < s)
    (q : CoarseEllipticityExponent) (omega : CutoffSample d) :
    0 ≤ cutoffUpperEllipticityLiteral M domainScale cutoffScale s q omega := by
  let : NeZero d := neZero_of_model_CutoffMultiscaleEllipticity M
  unfold cutoffUpperEllipticityLiteral
  rw [Ch04.LambdaSqCoeffField]
  simp only [dite_eq_left (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale
    omega)]
  exact Ch02.LambdaSq_nonneg (originCube d domainScale)
    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (Cutoff.coefficientCutoff M.nu cutoffScale omega)
      (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale omega)) hs q.2

/-- The actual inverse lower multiscale ellipticity: the literal, clamped at `0`. -/
noncomputable def cutoffLowerEllipticityInv (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (_hs : 0 < s)
    (q : CoarseEllipticityExponent) : CutoffSample d → ℝ :=
  fun omega => max 0 (cutoffLowerEllipticityInvLiteral M domainScale cutoffScale s q omega)

/-- The actual upper multiscale ellipticity: the literal, clamped at `0`. -/
noncomputable def cutoffUpperEllipticity (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (_hs : 0 < s)
    (q : CoarseEllipticityExponent) : CutoffSample d → ℝ :=
  fun omega => max 0 (cutoffUpperEllipticityLiteral M domainScale cutoffScale s q omega)

theorem measurable_cutoffLowerEllipticityInv (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : CoarseEllipticityExponent) :
    Measurable (cutoffLowerEllipticityInv M domainScale cutoffScale s hs q) :=
  measurable_const.max
    (measurable_cutoffLowerEllipticityInvLiteral M domainScale cutoffScale hs q)

theorem measurable_cutoffUpperEllipticity (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : CoarseEllipticityExponent) :
    Measurable (cutoffUpperEllipticity M domainScale cutoffScale s hs q) :=
  measurable_const.max
    (measurable_cutoffUpperEllipticityLiteral M domainScale cutoffScale hs q)

theorem cutoffLowerEllipticityInv_nonneg (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : CoarseEllipticityExponent) (omega : CutoffSample d) :
    0 ≤ cutoffLowerEllipticityInv M domainScale cutoffScale s hs q omega :=
  le_max_left _ _

theorem cutoffUpperEllipticity_nonneg (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : CoarseEllipticityExponent) (omega : CutoffSample d) :
    0 ≤ cutoffUpperEllipticity M domainScale cutoffScale s hs q omega :=
  le_max_left _ _

/-- **The exported inverse lower observable is its literal, at every sample
point.**  This is the payoff of the  body swap: the clamp is inert because the
literal is nonnegative on the source range `0 < s`. -/
theorem cutoffLowerEllipticityInv_eq_literal (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : CoarseEllipticityExponent) :
    cutoffLowerEllipticityInv M domainScale cutoffScale s hs q =
      cutoffLowerEllipticityInvLiteral M domainScale cutoffScale s q := by
  funext omega
  exact max_eq_right (cutoffLowerEllipticityInvLiteral_nonneg M domainScale cutoffScale hs q omega)

/-- **The exported upper observable is its literal, at every sample point.** -/
theorem cutoffUpperEllipticity_eq_literal (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : CoarseEllipticityExponent) :
    cutoffUpperEllipticity M domainScale cutoffScale s hs q =
      cutoffUpperEllipticityLiteral M domainScale cutoffScale s q := by
  funext omega
  exact max_eq_right (cutoffUpperEllipticityLiteral_nonneg M domainScale cutoffScale hs q omega)

theorem cutoffLowerEllipticityInv_ae_eq_literal (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : CoarseEllipticityExponent) :
    cutoffLowerEllipticityInv M domainScale cutoffScale s hs q =ᵐ[(Cutoff.cutoffSampleLaw
      M).toMeasure]
      cutoffLowerEllipticityInvLiteral M domainScale cutoffScale s q :=
  (cutoffLowerEllipticityInv_eq_literal M domainScale cutoffScale s hs q) ▸
    Filter.EventuallyEq.rfl

theorem cutoffUpperEllipticity_ae_eq_literal (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (hs : 0 < s)
    (q : CoarseEllipticityExponent) :
    cutoffUpperEllipticity M domainScale cutoffScale s hs q =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      cutoffUpperEllipticityLiteral M domainScale cutoffScale s q :=
  (cutoffUpperEllipticity_eq_literal M domainScale cutoffScale s hs q) ▸
    Filter.EventuallyEq.rfl

end

end Algsuperdiff.Section3.Observable
