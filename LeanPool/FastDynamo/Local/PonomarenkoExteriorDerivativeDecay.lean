/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.PonomarenkoCartesianExteriorDecay
public import LeanPool.FastDynamo.Local.PonomarenkoCartesianInteriorDerivative
public import LeanPool.FastDynamo.Local.PonomarenkoCartesianExteriorPhysicalDerivative
public import LeanPool.FastDynamo.Analysis.WholePlaneRadialExponential
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Exponential decay of the first Cartesian derivatives of the exterior Ponomarenko field

This module bounds the Cartesian first derivatives of the two transverse components of the
exterior Ponomarenko field (`exteriorComponentZeroDerivative`, `exteriorComponentOneDerivative`
of `Local/PonomarenkoCartesianExteriorPhysicalDerivative.lean`) on `‖y‖ ≥ 1` by a radial
exponential: `norm_exteriorComponentZeroDerivative_le_exp` and
`norm_exteriorComponentOneDerivative_le_exp`, with the envelope constants
`plusDerivativeConstant`, `minusDerivativeConstant`, `axialDerivativeConstant` and their sum
`derivativeConstant`.  `Local/HorizontalModeH1.lean` uses these bounds for the `H¹` membership
of the two-component mode of `lem:jump-horizontal-mode`, and
`Local/PonomarenkoExteriorSecondPartialBounds.lean` uses the constants.

The construction only assumes `0 < kappa.re`.  No `L²`, weak-derivative, `H1`, trace, or
operator-domain claim is made here.
-/

@[expose] public section

namespace FastDynamo
namespace PonomarenkoExteriorDerivativeDecay

noncomputable section

open Complex Metric MeasureTheory Set
open PonomarenkoCartesianExteriorDecay
open PonomarenkoCartesianInteriorDerivative
open PonomarenkoCartesianExteriorDerivative
open ComplexRadius
open WholePlaneRadialExponential

/-- A radius-one exponential-envelope constant for the derivative of the exterior
order-two (`plus`) radial branch. -/
def plusDerivativeConstant (kappa : ℂ) : ℝ :=
  ‖ModifiedBessel.I2 kappa‖ *
    (‖kappa‖ * (∫ t in Ioi (0 : ℝ),
      ‖ModifiedBessel.K1Integrand kappa t‖) +
      2 * (∫ t in Ioi (0 : ℝ),
        ‖ModifiedBessel.K2Integrand kappa t‖))

/-- A radius-one exponential-envelope constant for the derivative of the exterior
order-zero (`minus`) radial branch. -/
def minusDerivativeConstant (kappa : ℂ) : ℝ :=
  ‖ModifiedBessel.I0 kappa‖ * ‖kappa‖ *
    ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K1Integrand kappa t‖

/-- A radius-one exponential-envelope constant for the derivative of the exterior
axial order-one radial branch. -/
def axialDerivativeConstant (N : ℝ) (kappa : ℂ) : ℝ :=
  ‖ModifiedBessel.I1 kappa / (I * (N : ℂ))‖ *
    (‖kappa‖ * ((∫ t in Ioi (0 : ℝ),
      ‖ModifiedBessel.K0Integrand kappa t‖) +
      ∫ t in Ioi (0 : ℝ),
        ‖ModifiedBessel.K2Integrand kappa t‖))

/-- A common exterior derivative envelope, combining the three radial-derivative
constants with the transverse and axial phase-derivative contributions. -/
def derivativeConstant (N : ℝ) (kappa : ℂ) : ℝ :=
  minusDerivativeConstant kappa + plusDerivativeConstant kappa +
    axialDerivativeConstant N kappa + 4 * exteriorPlusDecayConstant kappa +
      2 * exteriorAxialDecayConstant N kappa

/-- The order-two exterior radial-derivative envelope constant is nonnegative, being built from
norms and integrals of norms. -/
theorem plusDerivativeConstant_nonneg (kappa : ℂ) :
    0 ≤ plusDerivativeConstant kappa := by
  unfold plusDerivativeConstant
  positivity

/-- The order-zero exterior radial-derivative envelope constant is nonnegative. -/
theorem minusDerivativeConstant_nonneg (kappa : ℂ) :
    0 ≤ minusDerivativeConstant kappa := by
  unfold minusDerivativeConstant
  positivity

/-- The axial exterior radial-derivative envelope constant is nonnegative. -/
theorem axialDerivativeConstant_nonneg (N : ℝ) (kappa : ℂ) :
    0 ≤ axialDerivativeConstant N kappa := by
  unfold axialDerivativeConstant
  positivity

/-- The combined exterior derivative envelope constant is nonnegative, being a positive
combination of the three radial constants and the two phase-decay constants. -/
theorem derivativeConstant_nonneg (N : ℝ) (kappa : ℂ) :
    0 ≤ derivativeConstant N kappa := by
  unfold derivativeConstant
  positivity [plusDerivativeConstant_nonneg kappa,
    minusDerivativeConstant_nonneg kappa,
    axialDerivativeConstant_nonneg N kappa,
    exteriorPlusDecayConstant_nonneg kappa,
    exteriorAxialDecayConstant_nonneg N kappa]

private theorem exteriorDerivative_triangle_le_exp
    (N : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re)
    (j : Fin 2) {y : WholePlane} (hy : 1 ≤ ‖y‖) :
    1 / 2 * (‖minusBranchDerivative kappa y (wholePlaneBasis j)‖ +
        ‖exteriorPhase y ^ 2 • plusBranchDerivative kappa y (wholePlaneBasis j) +
          plusOutsideReal kappa ‖y‖ • (2 • exteriorPhase y) •
            exteriorPhaseDerivative y (wholePlaneBasis j)‖) ≤
      Real.exp (-kappa.re * (‖y‖ - 1)) * derivativeConstant N kappa := by
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    norm_num at hy
  have hq := norm_exteriorPhase hy0
  have hdq := norm_exteriorPhaseDerivative_basis_le hy0 j
  have hvplus := norm_plusOutside_le_exp hkappa hy
  have hderivs := exterior_branch_derivative_exponential_bounds N hkappa hy
  have hdp := (norm_plusBranchDerivative_basis_le hy0 kappa j).trans hderivs.1
  have hdm := (norm_minusBranchDerivative_basis_le hy0 kappa j).trans hderivs.2.1
  let E : ℝ := Real.exp (-kappa.re * (‖y‖ - 1))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hdp' :
      ‖plusBranchDerivative kappa y (wholePlaneBasis j)‖ ≤
        E * plusDerivativeConstant kappa := by
    simpa [E, plusDerivativeConstant] using hdp
  have hdm' :
      ‖minusBranchDerivative kappa y (wholePlaneBasis j)‖ ≤
        E * minusDerivativeConstant kappa := by
    simpa [E, minusDerivativeConstant] using hdm
  have hvplus' : ‖plusOutsideReal kappa ‖y‖‖ ≤
      E * exteriorPlusDecayConstant kappa := by
    simpa [E, plusOutsideReal] using hvplus
  have hdq' : ‖exteriorPhaseDerivative y (wholePlaneBasis j)‖ ≤ 2 := by
    have hdiv : 2 / ‖y‖ ≤ 2 := by
      have hinv : 1 / ‖y‖ ≤ 1 := (div_le_one (by positivity)).2 hy
      calc
        2 / ‖y‖ = 2 * (1 / ‖y‖) := by ring
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = 2 := by ring
    exact hdq.trans hdiv
  have hradial :
      ‖exteriorPhase y ^ 2 • plusBranchDerivative kappa y (wholePlaneBasis j)‖ ≤
        E * plusDerivativeConstant kappa := by
    calc
      _ = ‖exteriorPhase y ^ 2‖ *
          ‖plusBranchDerivative kappa y (wholePlaneBasis j)‖ := norm_smul _ _
      _ = ‖plusBranchDerivative kappa y (wholePlaneBasis j)‖ := by
        rw [norm_pow, hq]
        norm_num
      _ ≤ E * plusDerivativeConstant kappa := hdp'
  have hangular :
      ‖plusOutsideReal kappa ‖y‖ • (2 • exteriorPhase y) •
          exteriorPhaseDerivative y (wholePlaneBasis j)‖ ≤
        E * (4 * exteriorPlusDecayConstant kappa) := by
    rw [norm_smul, norm_smul, RCLike.norm_nsmul (K := ℂ), hq]
    norm_num only [nsmul_eq_mul, Nat.cast_ofNat, mul_one]
    calc
      ‖plusOutsideReal kappa ‖y‖‖ *
          (2 * ‖exteriorPhaseDerivative y (wholePlaneBasis j)‖) ≤
          (E * exteriorPlusDecayConstant kappa) * (2 * 2) := by
        gcongr
        exact mul_nonneg hE (exteriorPlusDecayConstant_nonneg kappa)
      _ = E * (4 * exteriorPlusDecayConstant kappa) := by ring
  have hcombined :
      ‖exteriorPhase y ^ 2 • plusBranchDerivative kappa y (wholePlaneBasis j) +
          plusOutsideReal kappa ‖y‖ • (2 • exteriorPhase y) •
            exteriorPhaseDerivative y (wholePlaneBasis j)‖ ≤
        E * (plusDerivativeConstant kappa + 4 * exteriorPlusDecayConstant kappa) := by
    calc
      _ ≤ ‖exteriorPhase y ^ 2 • plusBranchDerivative kappa y (wholePlaneBasis j)‖ +
          ‖plusOutsideReal kappa ‖y‖ • (2 • exteriorPhase y) •
            exteriorPhaseDerivative y (wholePlaneBasis j)‖ := norm_add_le _ _
      _ ≤ E * plusDerivativeConstant kappa +
          E * (4 * exteriorPlusDecayConstant kappa) := add_le_add hradial hangular
      _ = _ := by ring
  calc
    _ ≤ 1 / 2 * (E * minusDerivativeConstant kappa +
          E * (plusDerivativeConstant kappa + 4 * exteriorPlusDecayConstant kappa)) :=
      mul_le_mul_of_nonneg_left (add_le_add hdm' hcombined) (by norm_num)
    _ ≤ E * derivativeConstant N kappa := by
      unfold derivativeConstant
      nlinarith [minusDerivativeConstant_nonneg kappa,
        plusDerivativeConstant_nonneg kappa,
        axialDerivativeConstant_nonneg N kappa,
        exteriorPlusDecayConstant_nonneg kappa,
        exteriorAxialDecayConstant_nonneg N kappa]

/-- Exponential decay of the first Cartesian partial of the exterior mode's first component:
for `Re κ > 0` and `‖y‖ ≥ 1` its norm is at most `exp(-(Re κ)(‖y‖-1))` times the envelope
constant. -/
theorem norm_exteriorComponentZeroDerivative_le_exp
    (N : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re)
    (j : Fin 2) {y : WholePlane} (hy : 1 ≤ ‖y‖) :
    ‖exteriorComponentZeroDerivative kappa y (wholePlaneBasis j)‖ ≤
      Real.exp (-kappa.re * (‖y‖ - 1)) * derivativeConstant N kappa := by
  rw [exteriorComponentZeroDerivative]
  simp only [smul_apply, add_apply,
    Nat.reduceSub, pow_one]
  rw [norm_smul]
  rw [norm_inv]
  norm_num only [Complex.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
    (exteriorDerivative_triangle_le_exp N hkappa j hy)

/-- Exponential decay of the first Cartesian partial of the exterior mode's second component,
with the same envelope as the first component. -/
theorem norm_exteriorComponentOneDerivative_le_exp
    (N : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re)
    (j : Fin 2) {y : WholePlane} (hy : 1 ≤ ‖y‖) :
    ‖exteriorComponentOneDerivative kappa y (wholePlaneBasis j)‖ ≤
      Real.exp (-kappa.re * (‖y‖ - 1)) * derivativeConstant N kappa := by
  rw [exteriorComponentOneDerivative]
  simp only [smul_apply, sub_apply, add_apply, Nat.reduceSub, pow_one]
  rw [norm_smul, norm_smul, norm_inv]
  norm_num only [Complex.norm_I, Complex.norm_ofNat, one_mul]
  exact (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
    (exteriorDerivative_triangle_le_exp N hkappa j hy)

end
end PonomarenkoExteriorDerivativeDecay
end FastDynamo
