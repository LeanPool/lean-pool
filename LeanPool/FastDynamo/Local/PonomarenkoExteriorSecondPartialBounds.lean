/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.PonomarenkoExteriorSecondDerivative
public import LeanPool.FastDynamo.Local.PonomarenkoExteriorDerivativeDecay
public import LeanPool.FastDynamo.Local.PolarHessianCalculus

/-!
# Polar second partials of the exterior Ponomarenko branches and their exponential envelopes

This module assembles, from polar data, the ordered second Cartesian partials of the scalar
modes `B₋(r)` and `q² B₊(r)` built from the decaying exterior Bessel branches (singular only at
the polar axis), and bounds them by a radial exponential on the closed exterior of the unit
disk:

* the envelope constants `plusHessianConstant`, `minusHessianConstant`;
* the explicit polar values `radialCompositionPartialValue`,
  `phaseSquaredRadialSecondPartialValue`, `exteriorPlusSecondPartialValue`,
  `exteriorMinusSecondPartialValue`;
* the exponential envelopes `norm_exteriorPlusSecondPartialValue_le_exp` and
  `norm_exteriorMinusSecondPartialValue_le_exp`.

`Local/HorizontalModeExteriorSecondDerivatives.lean` uses the polar values and their
envelopes for the second derivatives of the exterior branch of the two-component mode of
`lem:jump-horizontal-mode`, and from them its exponential decay and `L²` membership.

Nothing here asserts `H²` regularity across the radius-one interface.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace PonomarenkoExteriorSecondPartialBounds

open Complex Metric MeasureTheory Set
open WholePlaneRadialExponential
open ComplexRadius
open PonomarenkoCartesianExteriorDecay
open PonomarenkoExteriorDerivativeDecay
open PonomarenkoCartesianExteriorDerivative
open PonomarenkoCartesianExteriorSecondDerivative
open PonomarenkoExteriorSecondDerivative
open PolarHessianCalculus

/-! ## Explicit envelope constants -/

/-- Envelope constant for the Hessian of the `q² plus` contribution.  The
coefficients respectively account for the radial Hessian, the two mixed
radial-angular terms, and the angular Hessian. -/
def plusHessianConstant (kappa : ℂ) : ℝ :=
  plusSecondDerivativeConstant kappa + 10 * plusDerivativeConstant kappa +
    20 * exteriorPlusDecayConstant kappa

/-- Envelope constant for the Hessian of the purely radial `minus`
contribution. -/
def minusHessianConstant (kappa : ℂ) : ℝ :=
  minusSecondDerivativeConstant kappa + 2 * minusDerivativeConstant kappa

/-- The Hessian envelope constant of the `q² B₊` contribution is nonnegative. -/
theorem plusHessianConstant_nonneg (kappa : ℂ) :
    0 ≤ plusHessianConstant kappa := by
  have hsecond : 0 ≤ plusSecondDerivativeConstant kappa := by
    unfold plusSecondDerivativeConstant
    exact mul_nonneg (norm_nonneg _)
      (K2SecondDerivativeConstant_nonneg kappa)
  unfold plusHessianConstant
  positivity [hsecond, plusDerivativeConstant_nonneg kappa,
    exteriorPlusDecayConstant_nonneg kappa]

/-- The Hessian envelope constant of the radial `B₋` contribution is nonnegative. -/
theorem minusHessianConstant_nonneg (kappa : ℂ) :
    0 ≤ minusHessianConstant kappa := by
  have hsecond : 0 ≤ minusSecondDerivativeConstant kappa := by
    unfold minusSecondDerivativeConstant
    exact mul_nonneg (norm_nonneg _)
      (K0SecondDerivativeConstant_nonneg kappa)
  unfold minusHessianConstant
  positivity [hsecond, minusDerivativeConstant_nonneg kappa]

/-! ## Explicit polar assembly of the second partials -/

/-- The first Cartesian partial value of a radial profile whose radial
derivative is `b'`. -/
def radialCompositionPartialValue
    (b' : ℂ) (y : WholePlane) (j : Fin 2) : ℂ :=
  radiusDerivative y (wholePlaneBasis j) • b'

/-- The ordered second partial of `q² b(r)`, expanded into one radial,
two mixed, and two angular terms. -/
def phaseSquaredRadialSecondPartialValue
    (b b' b'' : ℂ) (y : WholePlane) (j k : Fin 2) : ℂ :=
  exteriorPhase y ^ 2 *
      radialCompositionSecondPartialValue b' b'' y j k +
    2 * exteriorPhase y *
      exteriorPhaseDerivative y (wholePlaneBasis k) *
        radialCompositionPartialValue b' y j +
    2 * exteriorPhase y *
      exteriorPhaseDerivative y (wholePlaneBasis j) *
        radialCompositionPartialValue b' y k +
    2 * exteriorPhaseDerivative y (wholePlaneBasis k) *
      exteriorPhaseDerivative y (wholePlaneBasis j) * b +
    2 * exteriorPhase y * exteriorPhaseSecondPartial y j k * b

/-- The explicit second partial of the `q² plus` exterior contribution. -/
def exteriorPlusSecondPartialValue
    (kappa : ℂ) (y : WholePlane) (j k : Fin 2) : ℂ :=
  phaseSquaredRadialSecondPartialValue
    (plusOutsideReal kappa ‖y‖)
    (deriv (plusOutsideReal kappa) ‖y‖)
    (deriv (deriv (plusOutsideReal kappa)) ‖y‖) y j k

/-- The explicit second partial of the radial `minus` exterior contribution. -/
def exteriorMinusSecondPartialValue
    (kappa : ℂ) (y : WholePlane) (j k : Fin 2) : ℂ :=
  radialCompositionSecondPartialValue
    (deriv (minusOutsideReal kappa) ‖y‖)
    (deriv (deriv (minusOutsideReal kappa)) ‖y‖) y j k

/-- A coordinate direction picks up at most the full one-dimensional radial derivative:
`‖∂ⱼ b(‖y‖)‖ ≤ ‖b'‖` away from the origin, since `|⟪y, eⱼ⟫| ≤ ‖y‖`. -/
theorem norm_radialCompositionPartialValue_le
    {y : WholePlane} (hy : y ≠ 0) (b' : ℂ) (j : Fin 2) :
    ‖radialCompositionPartialValue b' y j‖ ≤ ‖b'‖ := by
  rw [radialCompositionPartialValue, norm_smul]
  calc
    ‖radiusDerivative y (wholePlaneBasis j)‖ * ‖b'‖ ≤ 1 * ‖b'‖ :=
      mul_le_mul_of_nonneg_right
        (norm_radiusDerivative_basis_le_one hy j) (norm_nonneg _)
    _ = ‖b'‖ := one_mul _

/-- On the closed exterior of the unit disk the coordinate derivative of the polar phase is
bounded by `2`, the general bound `2/‖y‖` improving there. -/
private theorem norm_exteriorPhaseDerivative_basis_le_two
    {y : WholePlane} (hy : 1 ≤ ‖y‖) (j : Fin 2) :
    ‖exteriorPhaseDerivative y (wholePlaneBasis j)‖ ≤ 2 := by
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    norm_num at hy
  have h := norm_exteriorPhaseDerivative_basis_le hy0 j
  have hdiv : 2 / ‖y‖ ≤ 2 := by
    have hinv : 1 / ‖y‖ ≤ 1 := (div_le_one (by positivity)).2 hy
    calc
      2 / ‖y‖ = 2 * (1 / ‖y‖) := by ring
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 2 := by ring
  exact h.trans hdiv

/-- On the closed exterior of the unit disk the second coordinate derivative of the polar phase
is bounded by `6`, the general bound `6/‖y‖²` improving there. -/
private theorem norm_exteriorPhaseSecondPartial_le_six
    {y : WholePlane} (hy : 1 ≤ ‖y‖) (j k : Fin 2) :
    ‖exteriorPhaseSecondPartial y j k‖ ≤ 6 := by
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    norm_num at hy
  have h := norm_exteriorPhaseSecondPartial_le hy0 j k
  have hsquare : 1 ≤ ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  exact h.trans (div_le_self (by norm_num : (0 : ℝ) ≤ 6) hsquare)

/-- On the closed exterior of the unit disk the second Cartesian partial of a radial composition
is bounded by `‖b''‖ + 2‖b'‖`. -/
private theorem norm_radialCompositionSecondPartialValue_le_unitExterior
    {y : WholePlane} (hy : 1 ≤ ‖y‖)
    (b' b'' : ℂ) (j k : Fin 2) :
    ‖radialCompositionSecondPartialValue b' b'' y j k‖ ≤
      ‖b''‖ + 2 * ‖b'‖ := by
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    norm_num at hy
  have h := norm_radialCompositionSecondPartialValue_le hy0 b' b'' j k
  have htwo : 2 / ‖y‖ ≤ 2 := by
    have hinv : 1 / ‖y‖ ≤ 1 := (div_le_one (by positivity)).2 hy
    calc
      2 / ‖y‖ = 2 * (1 / ‖y‖) := by ring
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 2 := by ring
  exact h.trans (add_le_add (le_refl ‖b''‖)
    (mul_le_mul_of_nonneg_right htwo (norm_nonneg b')))

/-- Coarse unit-exterior Hessian estimate for `q² b(r)`. -/
theorem norm_phaseSquaredRadialSecondPartialValue_le
    {y : WholePlane} (hy : 1 ≤ ‖y‖)
    (b b' b'' : ℂ) (j k : Fin 2) :
    ‖phaseSquaredRadialSecondPartialValue b b' b'' y j k‖ ≤
      ‖b''‖ + 10 * ‖b'‖ + 20 * ‖b‖ := by
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    norm_num at hy
  have hq : ‖exteriorPhase y‖ = 1 := norm_exteriorPhase hy0
  have hqj := norm_exteriorPhaseDerivative_basis_le_two hy j
  have hqk := norm_exteriorPhaseDerivative_basis_le_two hy k
  have hqjk := norm_exteriorPhaseSecondPartial_le_six hy j k
  have hbj := norm_radialCompositionPartialValue_le hy0 b' j
  have hbk := norm_radialCompositionPartialValue_le hy0 b' k
  have hbjk := norm_radialCompositionSecondPartialValue_le_unitExterior
    hy b' b'' j k
  have h₁ :
      ‖exteriorPhase y ^ 2 *
        radialCompositionSecondPartialValue b' b'' y j k‖ ≤
        ‖b''‖ + 2 * ‖b'‖ := by
    rw [norm_mul, norm_pow, hq]
    norm_num
    exact hbjk
  have h₂ :
      ‖2 * exteriorPhase y * exteriorPhaseDerivative y (wholePlaneBasis k) *
        radialCompositionPartialValue b' y j‖ ≤ 4 * ‖b'‖ := by
    simp only [norm_mul, hq, Complex.norm_ofNat]
    calc
      2 * 1 * ‖exteriorPhaseDerivative y (wholePlaneBasis k)‖ *
          ‖radialCompositionPartialValue b' y j‖ ≤ 2 * 1 * 2 * ‖b'‖ := by
        gcongr
      _ = 4 * ‖b'‖ := by ring
  have h₃ :
      ‖2 * exteriorPhase y * exteriorPhaseDerivative y (wholePlaneBasis j) *
        radialCompositionPartialValue b' y k‖ ≤ 4 * ‖b'‖ := by
    simp only [norm_mul, hq, Complex.norm_ofNat]
    calc
      2 * 1 * ‖exteriorPhaseDerivative y (wholePlaneBasis j)‖ *
          ‖radialCompositionPartialValue b' y k‖ ≤ 2 * 1 * 2 * ‖b'‖ := by
        gcongr
      _ = 4 * ‖b'‖ := by ring
  have h₄ :
      ‖2 * exteriorPhaseDerivative y (wholePlaneBasis k) *
        exteriorPhaseDerivative y (wholePlaneBasis j) * b‖ ≤ 8 * ‖b‖ := by
    simp only [norm_mul, Complex.norm_ofNat]
    calc
      2 * ‖exteriorPhaseDerivative y (wholePlaneBasis k)‖ *
          ‖exteriorPhaseDerivative y (wholePlaneBasis j)‖ * ‖b‖ ≤
          2 * 2 * 2 * ‖b‖ := by gcongr
      _ = 8 * ‖b‖ := by ring
  have h₅ :
      ‖2 * exteriorPhase y * exteriorPhaseSecondPartial y j k * b‖ ≤
        12 * ‖b‖ := by
    simp only [norm_mul, hq, Complex.norm_ofNat]
    calc
      2 * 1 * ‖exteriorPhaseSecondPartial y j k‖ * ‖b‖ ≤
          2 * 1 * 6 * ‖b‖ := by gcongr
      _ = 12 * ‖b‖ := by ring
  unfold phaseSquaredRadialSecondPartialValue
  calc
    ‖exteriorPhase y ^ 2 * radialCompositionSecondPartialValue b' b'' y j k +
        2 * exteriorPhase y * exteriorPhaseDerivative y (wholePlaneBasis k) *
          radialCompositionPartialValue b' y j +
        2 * exteriorPhase y * exteriorPhaseDerivative y (wholePlaneBasis j) *
          radialCompositionPartialValue b' y k +
        2 * exteriorPhaseDerivative y (wholePlaneBasis k) *
          exteriorPhaseDerivative y (wholePlaneBasis j) * b +
        2 * exteriorPhase y * exteriorPhaseSecondPartial y j k * b‖ ≤
      ‖exteriorPhase y ^ 2 * radialCompositionSecondPartialValue b' b'' y j k‖ +
        ‖2 * exteriorPhase y * exteriorPhaseDerivative y (wholePlaneBasis k) *
          radialCompositionPartialValue b' y j‖ +
        ‖2 * exteriorPhase y * exteriorPhaseDerivative y (wholePlaneBasis j) *
          radialCompositionPartialValue b' y k‖ +
        ‖2 * exteriorPhaseDerivative y (wholePlaneBasis k) *
          exteriorPhaseDerivative y (wholePlaneBasis j) * b‖ +
        ‖2 * exteriorPhase y * exteriorPhaseSecondPartial y j k * b‖ := by
      calc
        _ ≤ ‖exteriorPhase y ^ 2 *
                radialCompositionSecondPartialValue b' b'' y j k +
              2 * exteriorPhase y * exteriorPhaseDerivative y (wholePlaneBasis k) *
                radialCompositionPartialValue b' y j +
              2 * exteriorPhase y * exteriorPhaseDerivative y (wholePlaneBasis j) *
                radialCompositionPartialValue b' y k +
              2 * exteriorPhaseDerivative y (wholePlaneBasis k) *
                exteriorPhaseDerivative y (wholePlaneBasis j) * b‖ +
              ‖2 * exteriorPhase y * exteriorPhaseSecondPartial y j k * b‖ :=
            norm_add_le _ _
        _ ≤ _ := by
          gcongr
          calc
            _ ≤ ‖exteriorPhase y ^ 2 *
                    radialCompositionSecondPartialValue b' b'' y j k +
                  2 * exteriorPhase y *
                    exteriorPhaseDerivative y (wholePlaneBasis k) *
                      radialCompositionPartialValue b' y j +
                  2 * exteriorPhase y *
                    exteriorPhaseDerivative y (wholePlaneBasis j) *
                      radialCompositionPartialValue b' y k‖ +
                  ‖2 * exteriorPhaseDerivative y (wholePlaneBasis k) *
                    exteriorPhaseDerivative y (wholePlaneBasis j) * b‖ :=
                norm_add_le _ _
            _ ≤ _ := by
              gcongr
              calc
                _ ≤ ‖exteriorPhase y ^ 2 *
                        radialCompositionSecondPartialValue b' b'' y j k +
                      2 * exteriorPhase y *
                        exteriorPhaseDerivative y (wholePlaneBasis k) *
                          radialCompositionPartialValue b' y j‖ +
                      ‖2 * exteriorPhase y *
                        exteriorPhaseDerivative y (wholePlaneBasis j) *
                          radialCompositionPartialValue b' y k‖ := norm_add_le _ _
                _ ≤ _ := by
                  gcongr
                  exact norm_add_le _ _
    _ ≤ (‖b''‖ + 2 * ‖b'‖) + 4 * ‖b'‖ + 4 * ‖b'‖ +
        8 * ‖b‖ + 12 * ‖b‖ := by gcongr
    _ = ‖b''‖ + 10 * ‖b'‖ + 20 * ‖b‖ := by ring

/-- Exponential decay of the second Cartesian partial of the `q² B₊` contribution:
its norm is at most `exp(-(Re κ)(‖y‖-1))` times `plusHessianConstant κ`, combining the
radial value, first- and second-derivative envelopes with the phase bounds. -/
theorem norm_exteriorPlusSecondPartialValue_le_exp
    {kappa : ℂ} (hkappa : 0 < kappa.re)
    {y : WholePlane} (hy : 1 ≤ ‖y‖) (j k : Fin 2) :
    ‖exteriorPlusSecondPartialValue kappa y j k‖ ≤
      Real.exp (-kappa.re * (‖y‖ - 1)) * plusHessianConstant kappa := by
  have hzero := norm_plusOutside_le_exp hkappa hy
  have hfirst := (exterior_branch_derivative_exponential_bounds
    (0 : ℝ) hkappa hy).1
  have hsecond := (exterior_branch_secondDerivative_exponential_bounds
    (0 : ℝ) hkappa hy).1
  have hpolar := norm_phaseSquaredRadialSecondPartialValue_le hy
    (plusOutsideReal kappa ‖y‖)
    (deriv (plusOutsideReal kappa) ‖y‖)
    (deriv (deriv (plusOutsideReal kappa)) ‖y‖) j k
  let E : ℝ := Real.exp (-kappa.re * (‖y‖ - 1))
  change ‖exteriorPlusSecondPartialValue kappa y j k‖ ≤
    E * plusHessianConstant kappa
  change ‖plusOutsideReal kappa ‖y‖‖ ≤
    E * exteriorPlusDecayConstant kappa at hzero
  change ‖deriv (plusOutsideReal kappa) ‖y‖‖ ≤
    E * plusDerivativeConstant kappa at hfirst
  change ‖deriv (deriv (plusOutsideReal kappa)) ‖y‖‖ ≤
    E * plusSecondDerivativeConstant kappa at hsecond
  unfold exteriorPlusSecondPartialValue
  calc
    _ ≤ ‖deriv (deriv (plusOutsideReal kappa)) ‖y‖‖ +
        10 * ‖deriv (plusOutsideReal kappa) ‖y‖‖ +
        20 * ‖plusOutsideReal kappa ‖y‖‖ := hpolar
    _ ≤ E * plusSecondDerivativeConstant kappa +
        10 * (E * plusDerivativeConstant kappa) +
        20 * (E * exteriorPlusDecayConstant kappa) := by gcongr
    _ = E * plusHessianConstant kappa := by
      unfold plusHessianConstant
      ring

/-- Exponential decay of the second Cartesian partial of the radial `B₋` contribution, with
envelope `minusHessianConstant κ`. -/
theorem norm_exteriorMinusSecondPartialValue_le_exp
    (N : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re)
    {y : WholePlane} (hy : 1 ≤ ‖y‖) (j k : Fin 2) :
    ‖exteriorMinusSecondPartialValue kappa y j k‖ ≤
      Real.exp (-kappa.re * (‖y‖ - 1)) * minusHessianConstant kappa := by
  have hfirst := (exterior_branch_derivative_exponential_bounds N hkappa hy).2.1
  have hsecond :=
    (exterior_branch_secondDerivative_exponential_bounds N hkappa hy).2.1
  have hpolar := norm_radialCompositionSecondPartialValue_le_unitExterior hy
    (deriv (minusOutsideReal kappa) ‖y‖)
    (deriv (deriv (minusOutsideReal kappa)) ‖y‖) j k
  let E : ℝ := Real.exp (-kappa.re * (‖y‖ - 1))
  change ‖exteriorMinusSecondPartialValue kappa y j k‖ ≤
    E * minusHessianConstant kappa
  change ‖deriv (minusOutsideReal kappa) ‖y‖‖ ≤
    E * minusDerivativeConstant kappa at hfirst
  change ‖deriv (deriv (minusOutsideReal kappa)) ‖y‖‖ ≤
    E * minusSecondDerivativeConstant kappa at hsecond
  unfold exteriorMinusSecondPartialValue
  calc
    _ ≤ ‖deriv (deriv (minusOutsideReal kappa)) ‖y‖‖ +
        2 * ‖deriv (minusOutsideReal kappa) ‖y‖‖ := hpolar
    _ ≤ E * minusSecondDerivativeConstant kappa +
        2 * (E * minusDerivativeConstant kappa) := by gcongr
    _ = E * minusHessianConstant kappa := by
      unfold minusHessianConstant
      ring

end PonomarenkoExteriorSecondPartialBounds
end FastDynamo
