/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.IncrementOscillation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.ResponseCongruence

/-!
# JSmallness

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The corrected response-`J` smallness gate on a good cube

This module proves a local version of the display `e.we.can.apply.cg` of ABK26,
the `J`-smallness step of `p.bfA.multiscalebound`:

```
3^{2j} ||grad (k_L - k_j)||_{W^{1,infinity}(z+square_j)} 1_{not B(spx)}
  <=  delta_osc c_star^{1/2} gamma^{-1/2} 3^{gamma j}
  <=  2^{-5} C_{(e.J.sensitivity.smallness.condition)}^{-1} sigmabar_j
  <=  C_{(e.J.sensitivity.smallness.condition)}^{-1} lambda_{1/4,2}(z+square_j; a_j) ,
```

and then transfers the last gauge to the exponent the frozen Section 2.4
sensitivity lemmas consume.

## The three inequalities

* The first is the complement control of `e.Bosc.def`, proved as
  `incrementOscGauge_le_oscThreshold` (`IncrementOscillation.lean`).
* The second is the induction-state clause `e.shom.h.bounds` combined with
  `e.delta.osc.choice`, proved as
  `oscThreshold_le_two_pow_neg_nine_mul_inv_lambdaSensitivityConst_mul_sigmaBar`
  (`LambdaSensitivityTwin.lean`), at the `lambda`-sensitivity constant the
  chain below is read against.
  The factor used here is `2^{-9}`, which is below the manuscript's `2^{-5}`.
* The third is the complement of `e.Bloc.def`:
  `lambda^{-1}_{1/4,2}(z+square_j; a_j) <= 10 sigma_j^{-1}`, i.e.
  `sigmabar_j <= 10 lambda_{1/4,2}(z+square_j; a_j)`, which proves the final
  local inequality in the chain
  because `2^{-9} . 10 < 1`.

## The exponent correction

The passage is the exponent monotonicity `e.ellipticities.monotone.ordered` at
`1/4 < 3/8` composed with the translation-and-dilation covariance of
`lambda_{s,q}`, i.e. the general
`lambdaSq_le_unitCubeLambda_unitRescaledCutoffCoeff` of `LambdaTransfer.lean`
read at `t = 1/4`; the manuscript's own inequality is the stronger one, so no
strength is lost.

## Why the assembled statements are almost-sure

`e.Bloc.def` is stated against the *measurable representative*
`cubeLowerEllipticityInv` built by `A.mk`, of which no pointwise information is
available; the last inequality of the chain divides by it and so needs its
positivity, which holds almost surely (`cubeLowerEllipticityInv_pos_ae`).  The
same carrier phenomenon already governs `lambda_transfer_ae` in
`LambdaTransfer.lean`.  Every statement below is proved first in pointwise form
with the positivity as an explicit binder, and then almost surely with that
binder discharged.

## Main results

* `sigmaBar_le_ten_mul_cubeLowerEllipticity_of_notMem_badLoc`: the `not B_loc`
  arithmetic.
* `lambda_transfer_quarter_literal`, `lambda_transfer_quarter_ae`: the
  `t = 1/4` instance of the lambda-transfer, in pointwise and in
  almost-sure form.

## References

* ABK26, `p.bfA.multiscalebound`, `e.we.can.apply.cg`.
* ABK26, `e.Bosc.def`, `e.delta.osc.choice`, `e.Bloc.def`.
* ABK26, `e.ellipticities.monotone.ordered`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The `not B_loc` arithmetic -/

/-- The complement of `e.Bloc.def` (ABK26), read as a lower bound on the
coarse-grained lower ellipticity: since `lambda^{-1}_{1/4,2}(z+square_j; a_j)
<= 10 sigma_j^{-1}`, we have `sigmabar_j <= 10 lambda_{1/4,2}(z+square_j;
a_j)`. -/
theorem sigmaBar_le_ten_mul_cubeLowerEllipticity_of_notMem_badLoc (M : ABKModel d)
    (Q : TriadicCube d) {omega : CutoffSample d} (homega : omega ∉ badLoc M Q)
    (hpos : 0 < cubeLowerEllipticityInv M Q Q.scale (1 / 4) (by norm_num)
      exponentTwo omega) :
    ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) ≤
      10 * cubeLowerEllipticity M Q Q.scale (1 / 4) (by norm_num) exponentTwo
        omega := by
  have hsig : (0 : ℝ) < ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale).2
  have hnot : ¬ (10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ))⁻¹ <
      cubeLowerEllipticityInv M Q Q.scale (1 / 4) (by norm_num) exponentTwo omega) :=
    fun hcon => homega (Set.mem_union_left _ hcon)
  have hle : cubeLowerEllipticityInv M Q Q.scale (1 / 4) (by norm_num) exponentTwo
      omega ≤ 10 * ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ))⁻¹ :=
    not_lt.1 hnot
  have hmul := mul_le_mul_of_nonneg_right hle hsig.le
  rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hsig), mul_one] at hmul
  have hcomm : ((Algsuperdiff.Section3.Annealed.sigmaBar M Q.scale : ℝ)) *
      cubeLowerEllipticityInv M Q Q.scale (1 / 4) (by norm_num) exponentTwo omega
        ≤ 10 := by linarith [hmul]
  have hscaled := mul_le_mul_of_nonneg_right hcomm
    (inv_nonneg.2 hpos.le : (0 : ℝ) ≤
      (cubeLowerEllipticityInv M Q Q.scale (1 / 4) (by norm_num) exponentTwo
        omega)⁻¹)
  rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one] at hscaled

/-! ## The lambda-transfer at `t = 1/4` -/

/-- **The lambda-transfer at the exponent of `e.Bloc.def`, at the literal
observable.**  The manuscript's `lambda_{1/4,2}(z + square_m; a_n)` is below the
frozen Section 2.4 unit-cube gauge `lambda_{3/8,2}` of the rescaled coefficient
field.  This is `e.ellipticities.monotone.ordered` at `1/4 < 3/8` composed with
the translation-and-dilation covariance of `lambda_{s,q}`. -/
theorem lambda_transfer_quarter_literal (M : ABKModel d) (Q : TriadicCube d)
    (n : ℤ) (omega : CutoffSample d) :
    (cubeLowerEllipticityInvLiteral M Q n (1 / 4) exponentTwo omega)⁻¹ ≤
      unitCubeLambda (3 / 8) (.finite 2)
        (unitRescaledCutoffCoeff M Q n omega) := by
  rw [cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq, exponentTwo_val]
  exact lambdaSq_le_unitCubeLambda_unitRescaledCutoffCoeff M Q n (by norm_num)
    (by norm_num) (by norm_num) omega

/-- **The lambda-transfer at `t = 1/4`, at the representative used by
`e.Bloc.def`.** -/
theorem lambda_transfer_quarter_ae (M : ABKModel d) (Q : TriadicCube d) (n : ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      cubeLowerEllipticity M Q n (1 / 4) (by norm_num) exponentTwo omega ≤
        unitCubeLambda (3 / 8) (.finite 2)
          (unitRescaledCutoffCoeff M Q n omega) := by
  filter_upwards [cubeLowerEllipticity_ae_eq_literal M Q n (1 / 4) (by norm_num)
    exponentTwo] with omega homega
  rw [homega]
  exact lambda_transfer_quarter_literal M Q n omega

end

end Algsuperdiff.Section3.Provider.BadEvents
