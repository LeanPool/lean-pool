/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.GoodLocalEvents
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ExponentMonotonicity

/-!
# LambdaTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The lambda-transfer, and the unconditional good-event gates

`GoodLocalEvents.lean` delivers the gate opening of ABK26 in two
layers: the unconditional cube-level bound against
`lambda_{1/8,2}(z + square_m; a_n)`, and four helpers named
`..._of_lambdaTransfer` which carry the missing comparison

```
lambda_{1/8,2}(z + square_m; a_n)  <=  unitCubeLambda (3/8) 2 (a rescaled)
```

as an explicit binder.  This module supplies that comparison and discharges the
binder.

## The two inputs

* **Exponent monotonicity** `e.ellipticities.monotone.ordered` (ABK26), proved
  locally in
  `Algsuperdiff.Section3.Provider.ErrorComparison.ExponentMonotonicity`; here at
  the instance `t = 1/8 < 3/8 = s`, `q = 2`.
* **Translation and dilation covariance** of `lambda_{s,q}`, proved locally in
  `LambdaCovariance.lean`:
  `unitCubeLambda s q (unitRescaledCutoffCoeff M Q n omega) =
   lambda_{s,q}(Q; a_n(omega))`.

## Why the discharged gates are almost-sure statements

The event `goodLocalEvent` is stated against `cubeLowerEllipticity`, the
*measurable representative* of `lambda_{1/8,2}(Q; a_n)` built in
`CubeEllipticity.lean` from `A.mk`.  A measurable representative agrees with
the literal observable only almost everywhere, and no pointwise information
about it is available.  The comparison is therefore proved

* pointwise, at the literal observable
  (`lambda_transfer_literal`), and
* almost surely, at the representative (`lambda_transfer_ae`),

and the discharged gates inherit the almost-sure quantifier.  This is a carrier
consequence of the repository's representative construction, not a weakening of
the manuscript statement; the manuscript's `lambda_{1/8,2}` is the literal
observable, for which the transfer is unconditional and pointwise.

## Main results

* `lambda_transfer_literal`: the pointwise comparison at the literal
  multiscale observable.
* `lambda_transfer_ae`: the same comparison at the representative used by
  `goodLocalEvent`, almost surely.
* `gradientW1Infinity_incrementUnitCube₂_le_lambdaGate_ae`,
  `gradientW1Infinity_incrementUnitCube₂_le_responseGate_ae`,
  `lambda_sensitivity_of_mem_goodLocalEvent_ae`: three conditional helpers of
  `GoodLocalEvents.lean`, with the `hlam` binder discharged.
* `perturbCoeffOn_unitRescaledCutoffCoeff_toCoeffField_ae_eq`: the
  identification `a_L(z + 3^m .) = a_n(z + 3^m .) + (k_L - k_n)(z + 3^m .)` at
  the unit-cube carrier, needed by the `#J`-smallness consumer (ABK26).

## References

* ABK26, `e.good.local.events`.
* ABK26, `e.ellipticities.monotone.ordered`.
* ABK26 (the `#J`-smallness consumer).
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- Nonzero dimension, from the paper-wide assumption `2 <= d` stored in the
model. -/
private theorem neZero_of_model_lambdaTransfer (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-! ## The literal multiscale observable of the cutoff -/

/-- The exponent carrier `q = 2` of `e.good.local.events` is CoarseGraining's
finite exponent `2`. -/
theorem exponentTwo_val :
    (exponentTwo : Algsuperdiff.Section3.CoarseEllipticityExponent).1 =
      (.finite 2 : Ch02.MultiscaleExponent) :=
  rfl

/-- The literal observable of `CubeEllipticity.lean` is CoarseGraining's
`Ch02.lambdaSq` of the compatible triadic family of the actual cutoff. -/
theorem cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (q : Algsuperdiff.Section3.CoarseEllipticityExponent)
    (omega : CutoffSample d) :
    (cubeLowerEllipticityInvLiteral M Q cutoffScale s q omega)⁻¹ =
      Ch02.lambdaSq Q s q.1
        (coefficientCutoffTriadicCoeffFamily M cutoffScale omega) := by
  let : NeZero d := neZero_of_model_lambdaTransfer M
  rw [cubeLowerEllipticityInvLiteral_inv_eq, Ch04.lambdaSqCoeffField]
  simp only [dite_eq_left
    (coefficientCutoff_aeLocallyUniformlyEllipticField M cutoffScale omega)]
  exact Ch02.lambdaSq_eq_ofAEEq (fun _ => Filter.EventuallyEq.rfl) Q s q.1

/-! ## The lambda-transfer -/

/-- **The lambda-transfer, in general form.**  For every `0 < t < s` and every
admissible `q`, the manuscript's `lambda_{t,q}(z + square_m; a_n)` is below the
frozen Section 2.4 unit-cube gauge `lambda_{s,q}` of the rescaled coefficient
field.  This is the composition of the exponent monotonicity
`e.ellipticities.monotone.ordered` with the translation-and-dilation covariance
of `lambda_{s,q}`. -/
theorem lambdaSq_le_unitCubeLambda_unitRescaledCutoffCoeff (M : ABKModel d)
    (Q : TriadicCube d) (n : ℤ) {t s : ℝ} {q : Ch02.MultiscaleExponent}
    (ht : 0 < t) (hts : t < s) (hq : q.IsAdmissible) (omega : CutoffSample d) :
    Ch02.lambdaSq Q t q (coefficientCutoffTriadicCoeffFamily M n omega) ≤
      unitCubeLambda s q (unitRescaledCutoffCoeff M Q n omega) := by
  let : NeZero d := neZero_of_model_lambdaTransfer M
  rw [unitCubeLambda_unitRescaledCutoffCoeff]
  exact ErrorComparison.lambdaSq_mono_of_lt Q
    (coefficientCutoffTriadicCoeffFamily M n omega) ht hts hq

/-- **The lambda-transfer, at the literal observable.**  The manuscript's
`lambda_{1/8,2}(z + square_m; a_n)` is below the frozen Section 2.4 unit-cube
gauge `lambda_{3/8,2}` of the rescaled coefficient field.  This is the
composition of the exponent monotonicity `e.ellipticities.monotone.ordered` at
`1/8 < 3/8` with the translation-and-dilation covariance of `lambda_{s,q}`. -/
theorem lambda_transfer_literal (M : ABKModel d) (Q : TriadicCube d) (n : ℤ)
    (omega : CutoffSample d) :
    (cubeLowerEllipticityInvLiteral M Q n (1 / 8) exponentTwo omega)⁻¹ ≤
      unitCubeLambda (3 / 8) (.finite 2)
        (unitRescaledCutoffCoeff M Q n omega) := by
  rw [cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq, exponentTwo_val]
  exact lambdaSq_le_unitCubeLambda_unitRescaledCutoffCoeff M Q n (by norm_num)
    (by norm_num) (by norm_num) omega

/-- **The lambda-transfer, at the representative used by the good event.**
Almost surely, the event's own `cubeLowerEllipticity` is below the frozen
unit-cube gauge of the rescaled coefficient field. -/
theorem lambda_transfer_ae (M : ABKModel d) (Q : TriadicCube d) (n : ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      cubeLowerEllipticity M Q n (1 / 8) (by norm_num) exponentTwo omega ≤
        unitCubeLambda (3 / 8) (.finite 2)
          (unitRescaledCutoffCoeff M Q n omega) := by
  filter_upwards [cubeLowerEllipticity_ae_eq_literal M Q n (1 / 8) (by norm_num)
    exponentTwo] with omega homega
  rw [homega]
  exact lambda_transfer_literal M Q n omega

/-! ## The unconditional gates -/

/-- **The frozen `lambda`-sensitivity gate on the good event**, unconditional:
the `_of_lambdaTransfer` binder of `GoodLocalEvents.lean` is discharged by
`lambda_transfer_ae`. -/
theorem gradientW1Infinity_incrementUnitCube₂_le_lambdaGate_ae (M : ABKModel d)
    (Ccg : ℝ) (Q : TriadicCube d) (n L : ℤ) (hL : n ≤ L) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q n →
        (incrementUnitCube₂ Q n L omega).gradientW1Infinity ≤
          (lambdaSensitivityConst d)⁻¹ *
            unitCubeLambda (3 / 8) (.finite 2)
              (unitRescaledCutoffCoeff M Q n omega) := by
  filter_upwards [lambda_transfer_ae M Q n] with omega htransfer homega
  exact gradientW1Infinity_incrementUnitCube₂_le_lambdaGate_of_lambdaTransfer
    M Q homega hL _ htransfer

/-- **The frozen response-sensitivity gate on the good event**, unconditional. -/
theorem gradientW1Infinity_incrementUnitCube₂_le_responseGate_ae (M : ABKModel d)
    (Ccg : ℝ) (Q : TriadicCube d) (n L : ℤ) (hL : n ≤ L) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q n →
        (incrementUnitCube₂ Q n L omega).gradientW1Infinity ≤
          (responseSensitivityConst d)⁻¹ *
            unitCubeLambda (3 / 8) (.finite 2)
              (unitRescaledCutoffCoeff M Q n omega) := by
  filter_upwards [lambda_transfer_ae M Q n] with omega htransfer homega
  exact gradientW1Infinity_incrementUnitCube₂_le_responseGate_of_lambdaTransfer
    M Q homega hL _ htransfer

/-- **The `lambda`-sensitivity switch on the good event**, unconditional: the
coefficient switch of ABK26, in the form used. -/
theorem lambda_sensitivity_of_mem_goodLocalEvent_ae (M : ABKModel d) (Ccg : ℝ)
    (Q : TriadicCube d) (n L : ℤ) (hL : n ≤ L) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    (hq : q.IsAdmissible) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q n →
        (unitCubeLambda s q
          (perturbCoeffOn (cubeDomain (originCube d 0))
            (unitRescaledCutoffCoeff M Q n omega)
            (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn 1))⁻¹
          ≤ (1 + lambdaSensitivityConst d *
              (incrementUnitCube₂ Q n L omega).gradientW1Infinity *
              (unitCubeLambda (3 / 8) (.finite 2)
                (unitRescaledCutoffCoeff M Q n omega))⁻¹) *
            (unitCubeLambda s q (unitRescaledCutoffCoeff M Q n omega))⁻¹ := by
  filter_upwards [lambda_transfer_ae M Q n] with omega htransfer homega
  exact lambda_sensitivity_of_mem_goodLocalEvent_of_lambdaTransfer M Q homega hL
    _ htransfer s q hs hs2 hq

/-! ## The perturbed unit-cube coefficient is the rescaled `a_L` -/

/-- The base point of a triadic cube, as used by the increment rescaling, is
CoarseGraining's `triadicCubeShift`. -/
theorem cubeBasePoint_eq_triadicCubeShift (Q : TriadicCube d) :
    cubeBasePoint Q = triadicCubeShift Q :=
  rfl

/-- **The `#J`-smallness identification** (ABK26).  At the unit-cube carrier,
the frozen perturbation of the rescaled `a_n` by the rescaled literal increment
`k_L - k_n` is the rescaled `a_L`:

```
a_L(z + 3^m y)  =  a_n(z + 3^m y) + (k_L - k_n)(z + 3^m y)
```

almost everywhere on the open unit cube. -/
theorem perturbCoeffOn_unitRescaledCutoffCoeff_toCoeffField_ae_eq
    (M : ABKModel d) (Q : TriadicCube d) {n L : ℤ} (hnL : n ≤ L)
    (omega : CutoffSample d) :
    (perturbCoeffOn (cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M Q n omega)
        (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn 1).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (originCube d 0))]
      fun y : Vec d =>
        coefficientCutoff M.nu L omega
          (((3 : ℝ) ^ Q.scale) • y + triadicCubeShift Q) := by
  filter_upwards [unitRescaledCutoffCoeff_toCoeffField_ae_eq M Q n omega]
    with y hy
  change (unitRescaledCutoffCoeff M Q n omega).toCoeffField y +
      (1 : ℝ) • (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn.1.1 y =
    coefficientCutoff M.nu L omega (((3 : ℝ) ^ Q.scale) • y + triadicCubeShift Q)
  rw [hy, incrementUnitCube₂_value Q hnL omega y, cubeBasePoint_eq_triadicCubeShift,
    one_smul, coefficientCutoff_apply, coefficientCutoff_apply]
  abel

end

end Algsuperdiff.Section3.Provider.BadEvents
