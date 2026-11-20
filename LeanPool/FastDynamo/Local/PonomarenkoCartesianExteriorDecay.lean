/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.ComplexRadius
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Exponential bounds for the exterior Ponomarenko branches

This module gives explicit exponential majorants on `r ≥ 1` for the two transverse exterior
modified-Bessel branches of the cross-normalized Ponomarenko mode, `norm_plusOutside_le_exp`
and `norm_minusOutside_le_exp`, with the constants `exteriorPlusDecayConstant` and
`exteriorMinusDecayConstant` (and the axial constant `exteriorAxialDecayConstant`, used by
`Local/PonomarenkoExteriorDerivativeDecay.lean`).  The branch bounds are used for the decay of the
two-component mode and of its derivatives (`Local/HorizontalModeBranches.lean`,
`Local/PonomarenkoExteriorDerivativeDecay.lean`,
`Local/PonomarenkoExteriorSecondPartialBounds.lean`).

The only analytic assumption is `0 < kappa.re`.  No integrability, weak derivative, `H1`,
distributional-divergence, or operator-domain claim is made here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set Metric Real

namespace PonomarenkoCartesianExteriorDecay

open ComplexRadius
open PonomarenkoCrossNormalizedJump
open PonomarenkoCrossNormalizedAxial
open ModifiedBesselBoundaryBehavior

/-- The fixed order-two exterior majorant at radius one. -/
def exteriorPlusDecayConstant (kappa : ℂ) : ℝ :=
  ‖ModifiedBessel.I2 kappa‖ *
    ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K2Integrand kappa t‖

/-- The fixed order-zero exterior majorant at radius one. -/
def exteriorMinusDecayConstant (kappa : ℂ) : ℝ :=
  ‖ModifiedBessel.I0 kappa‖ *
    ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K0Integrand kappa t‖

/-- The fixed axial order-one exterior majorant at radius one. -/
def exteriorAxialDecayConstant (N : ℝ) (kappa : ℂ) : ℝ :=
  (‖ModifiedBessel.I1 kappa‖ / ‖Complex.I * (N : ℂ)‖) *
    ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K1Integrand kappa t‖

/-- The order-two exterior majorant constant is nonnegative, being a norm times the integral of a
norm. -/
theorem exteriorPlusDecayConstant_nonneg (kappa : ℂ) :
    0 ≤ exteriorPlusDecayConstant kappa := by
  unfold exteriorPlusDecayConstant
  positivity

/-- The order-zero exterior majorant constant is nonnegative. -/
theorem exteriorMinusDecayConstant_nonneg (kappa : ℂ) :
    0 ≤ exteriorMinusDecayConstant kappa := by
  unfold exteriorMinusDecayConstant
  positivity

/-- The axial order-one exterior majorant constant is nonnegative. -/
theorem exteriorAxialDecayConstant_nonneg (N : ℝ) (kappa : ℂ) :
    0 ≤ exteriorAxialDecayConstant N kappa := by
  unfold exteriorAxialDecayConstant
  positivity

/-- Explicit exponential decay of the exterior order-two branch. -/
theorem norm_plusOutside_le_exp
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 1 ≤ r) :
    ‖plusOutside kappa (r : ℂ)‖ ≤
      Real.exp (-kappa.re * (r - 1)) * exteriorPlusDecayConstant kappa := by
  have hK := (modifiedBessel_K012_radial_exponential_bounds hkappa hr).2.2
  rw [plusOutside, norm_mul]
  calc
    ‖ModifiedBessel.I2 kappa‖ * ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖ ≤
        ‖ModifiedBessel.I2 kappa‖ *
          (Real.exp (-kappa.re * (r - 1)) *
            ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K2Integrand kappa t‖) :=
      mul_le_mul_of_nonneg_left hK (norm_nonneg _)
    _ = Real.exp (-kappa.re * (r - 1)) * exteriorPlusDecayConstant kappa := by
      unfold exteriorPlusDecayConstant
      ring

/-- Explicit exponential decay of the exterior order-zero branch. -/
theorem norm_minusOutside_le_exp
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 1 ≤ r) :
    ‖minusOutside kappa (r : ℂ)‖ ≤
      Real.exp (-kappa.re * (r - 1)) * exteriorMinusDecayConstant kappa := by
  have hK := (modifiedBessel_K012_radial_exponential_bounds hkappa hr).1
  rw [minusOutside, norm_mul, norm_neg]
  calc
    ‖ModifiedBessel.I0 kappa‖ * ‖ModifiedBessel.K0 (kappa * (r : ℂ))‖ ≤
        ‖ModifiedBessel.I0 kappa‖ *
          (Real.exp (-kappa.re * (r - 1)) *
            ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K0Integrand kappa t‖) :=
      mul_le_mul_of_nonneg_left hK (norm_nonneg _)
    _ = Real.exp (-kappa.re * (r - 1)) * exteriorMinusDecayConstant kappa := by
      unfold exteriorMinusDecayConstant
      ring

end PonomarenkoCartesianExteriorDecay

end

end FastDynamo
