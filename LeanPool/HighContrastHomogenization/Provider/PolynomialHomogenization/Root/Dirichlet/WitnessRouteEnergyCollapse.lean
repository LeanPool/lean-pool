/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessEnergyPriceAssembly
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.EnergyPriceEccentricityCollapse

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.WitnessRouteEnergyCollapse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The witness-route `Kenergy`, collapsed at a law-free amplitude listed five factors of the
scheduled-rate head.  Four were in hand;
the fifth — `Kenergy ≤ law-free × E^{d+2s₀+2q}` — was blocked because collapse applies to the
*shape* `gaugeWitnessEnergyPriceW C d s₀ (A · E^q) abar`
and that shape was produced by nothing, last row).  The module now produces exactly that shape, with
`A = lambdaRouteClaw · (witnessGeometricFactor · frameFoldConstant)`.

This module supplies the two pieces of glue that module did not carry:

* `witnessRouteCwit_eq_amplitude_mul_pow` — the associativity that exhibits
  `witnessRouteCwit` in shape, with `q = witnessErrorEccentricityExponent g κ`;
* `collapsedEnergyLawFree_mono` — monotonicity of the collapsed law-free
  constant in its amplitude, so that **any** law-free upper bound for `A` may be
  substituted after the collapse.

The combination is `witnessRouteEnergyPrice_le_collapsed`: the price at the
witness-route `Cwit` is below `collapsedEnergyLawFree C d s₀ Alaw` times a fixed
power of the witness eccentricity, for any `Alaw` dominating the amplitude.
The **only** thing left in the fifth factor is the explicit law-free `Alaw`,
whose three factors are each already
(`EnergyPrice.observationFillingCoefficient_le_of_residualWindow` for the λ-route
constant, the `witnessGeometricFactor_le_uniform` premise for the geometric factor,
and the `max_one_rpow_three_bracket_le` premise for the bracket factor of
`frameFoldConstant`).
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The witness-route `Cwit` in collapse shape. -/
theorem witnessRouteCwit_eq_amplitude_mul_pow (d : ℕ)
    (Claw Cgeo g kappaRate J : ℝ) (abar : Mat d) :
    witnessRouteCwit d Claw Cgeo g kappaRate J abar =
      (Claw * (Cgeo * frameFoldConstant d g kappaRate J)) *
        (max 1 (witnessEccentricity (symmPart abar))) ^
          witnessErrorEccentricityExponent g kappaRate := by
  rw [witnessRouteCwit]
  ring

/-- The witness-error eccentricity exponent is nonnegative on the printed
window. -/
theorem witnessErrorEccentricityExponent_nonneg {g kappaRate : ℝ}
    (hkappa : 0 < kappaRate)
    (hrho : 0 ≤ Certificate.printRowOrder g) :
    0 ≤ witnessErrorEccentricityExponent g kappaRate := by
  have hmax : (0 : ℝ) ≤ max (responseWindowOrder g) kappaRate :=
    le_trans hkappa.le (le_max_right _ _)
  have hden : (0 : ℝ) ≤ 2 * kappaRate := by positivity
  rw [witnessErrorEccentricityExponent]
  exact div_nonneg (mul_nonneg hrho hmax) hden

/-- The collapsed law-free constant is monotone in its amplitude. -/
theorem collapsedEnergyLawFree_mono (C : ℝ) {s A B : ℝ}
    (hs : 0 < s) (hA : 0 ≤ A) (hAB : A ≤ B) :
    collapsedEnergyLawFree C d s A ≤ collapsedEnergyLawFree C d s B := by
  have hsq : A ^ 2 ≤ B ^ 2 := by
    have hmul := mul_self_le_mul_self hA hAB
    simpa only [pow_two] using hmul
  have hC20 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
  have hsinv0 : (0 : ℝ) ≤ s⁻¹ := (inv_pos.mpr hs).le
  have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  have hCbesov0 : (0 : ℝ) ≤
      BufferToCell.positiveBesovContinuousComparisonConstant d :=
    (BufferToCell.positiveBesovContinuousComparisonConstant_pos d).le
  have hframe0 : (0 : ℝ) ≤ EnergyPrice.gaugeFrameConstant d s :=
    EnergyPrice.gaugeFrameConstant_nonneg d s
  rw [collapsedEnergyLawFree, collapsedEnergyLawFree]
  have hstep : C ^ 2 * s⁻¹ * (2 * (d : ℝ) * (A ^ 2 + 1)) ≤
      C ^ 2 * s⁻¹ * (2 * (d : ℝ) * (B ^ 2 + 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC20 hsinv0)
    exact mul_le_mul_of_nonneg_left (by linarith only [hsq]) hd0
  have hhead : (0 : ℝ) ≤ C ^ 2 * s⁻¹ * (2 * (d : ℝ) * (A ^ 2 + 1)) := by
    have : (0 : ℝ) ≤ A ^ 2 + 1 := by positivity
    exact mul_nonneg (mul_nonneg hC20 hsinv0) (mul_nonneg hd0 this)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hstep hCbesov0) hframe0

/-- **The fifth factor, in hand.**  The witness-route energy price collapses to
a law-free constant times a fixed power of the witness eccentricity, at any
law-free amplitude dominating the route's own. -/
theorem witnessRouteEnergyPrice_le_collapsed (C : ℝ)
    {g kappaRate s₀ Claw Cgeo J Alaw : ℝ} {abar : Mat d}
    (hs : 0 < s₀) (hkappa : 0 < kappaRate)
    (hrho : 0 ≤ Certificate.printRowOrder g)
    (hsd : 0 ≤ (d : ℝ) + 2 * s₀)
    (hA0 : 0 ≤ Claw * (Cgeo * frameFoldConstant d g kappaRate J))
    (hAle : Claw * (Cgeo * frameFoldConstant d g kappaRate J) ≤ Alaw) :
    EnergyPrice.gaugeWitnessEnergyPriceW C d s₀
        (witnessRouteCwit d Claw Cgeo g kappaRate J abar) abar ≤
      collapsedEnergyLawFree C d s₀ Alaw *
        (max 1 (witnessEccentricity (symmPart abar))) ^
          ((d : ℝ) + 2 * s₀ + 2 * witnessErrorEccentricityExponent g kappaRate)
      := by
  have hq : 0 ≤ witnessErrorEccentricityExponent g kappaRate :=
    witnessErrorEccentricityExponent_nonneg hkappa hrho
  have hE0 : (0 : ℝ) ≤ max 1 (witnessEccentricity (symmPart abar)) :=
    le_trans zero_le_one (le_max_left _ _)
  have hEpow : (0 : ℝ) ≤ (max 1 (witnessEccentricity (symmPart abar))) ^
      ((d : ℝ) + 2 * s₀ + 2 * witnessErrorEccentricityExponent g kappaRate) :=
    Real.rpow_nonneg hE0 _
  rw [witnessRouteCwit_eq_amplitude_mul_pow]
  refine le_trans (gaugeWitnessEnergyPriceW_le_collapsed C hs hq hsd abar) ?_
  exact mul_le_mul_of_nonneg_right
    (collapsedEnergyLawFree_mono C hs hA0 hAle) hEpow

end

end RowSupply
end HighContrast
end HCPolySupport
