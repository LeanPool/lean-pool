/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaTransfer

/-!
# ResponseCongruence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The perturbed rescaled coefficient is the rescaled `a_L`, for `responseJ`

`LambdaTransfer.lean` proves
`perturbCoeffOn_unitRescaledCutoffCoeff_toCoeffField_ae_eq`: the coefficient of
the frozen perturbation

```
perturbCoeffOn (unit cube) (a_n rescaled) (k_L - k_n rescaled) 1
```

agrees, almost everywhere on the open unit cube, with the rescaling `y |-> a_L(z
+ 3^m y)` of the literal cutoff `a_L` (ABK26).  `LambdaCovariance.lean` proves
the same description for the honest rescaled object `unitRescaledCutoffCoeff M Q
L omega`.

The consumer of the `#J`-smallness step needs the two objects to be
interchangeable inside `responseJ`.  Nothing analytic is reproved here; this
module records the identification of the two `CoeffOn` objects and reads the
congruence at it.

## Main results

* `perturbCoeffOn_unitRescaledCutoffCoeff_aeEq`: the two unit-cube coefficient
  objects are `CoeffOn.AEEq`.
* `responseJ_perturbCoeffOn_unitRescaledCutoffCoeff`: the `responseJ`
  congruence, `J(square_0, p, q; a_n + (k_L - k_n) rescaled) =
  J(square_0, p, q; a_L rescaled)`.
* `unitCubeLambda_perturbCoeffOn_unitRescaledCutoffCoeff`: the same
  identification read at the frozen unit-cube gauge, which is the form the
  `lambda`-sensitivity consumer needs.

## References

* ABK26 (`p.bfA.multiscalebound`, the `#J`-smallness consumer).
* ABK26, `e.good.local.events`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The two unit-cube coefficient objects agree almost everywhere -/

/-- **The `#J`-smallness identification, as a `CoeffOn` a.e. equality** (ABK26).
The frozen perturbation of the rescaled `a_n` by the rescaled literal increment
`k_L - k_n` is a.e. equal, on the open unit cube, to the rescaled `a_L`. -/
theorem perturbCoeffOn_unitRescaledCutoffCoeff_aeEq (M : ABKModel d)
    (Q : TriadicCube d) {n L : ℤ} (hnL : n ≤ L) (omega : CutoffSample d) :
    CoeffOn.AEEq
      (perturbCoeffOn (cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M Q n omega)
        (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn 1)
      (unitRescaledCutoffCoeff M Q L omega) :=
  (perturbCoeffOn_unitRescaledCutoffCoeff_toCoeffField_ae_eq M Q hnL omega).trans
    (unitRescaledCutoffCoeff_toCoeffField_ae_eq M Q L omega).symm

/-! ## The `responseJ` congruence -/

/-- **The `responseJ` congruence of the `#J`-smallness consumer** (ABK26).  The
frozen response functional of the perturbed rescaled `a_n` is the response
functional of the honest rescaled `a_L`. -/
theorem responseJ_perturbCoeffOn_unitRescaledCutoffCoeff (M : ABKModel d)
    (Q : TriadicCube d) {n L : ℤ} (hnL : n ≤ L) (omega : CutoffSample d)
    (p q : Vec d) :
    responseJ (cubeDomain (originCube d 0))
        (perturbCoeffOn (cubeDomain (originCube d 0))
          (unitRescaledCutoffCoeff M Q n omega)
          (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn 1) p q =
      responseJ (cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M Q L omega) p q :=
  Ch02.responseJ_eq_ofAEEq
    (perturbCoeffOn_unitRescaledCutoffCoeff_aeEq M Q hnL omega) p q

/-- The same identification at the frozen unit-cube multiscale gauge: the
`lambda`-sensitivity consumer of ABK26 reads its conclusion at `lambda_{s,q}` of
the perturbed object, which is `lambda_{s,q}` of the rescaled `a_L`. -/
theorem unitCubeLambda_perturbCoeffOn_unitRescaledCutoffCoeff (M : ABKModel d)
    (Q : TriadicCube d) {n L : ℤ} (hnL : n ≤ L) (omega : CutoffSample d) (s : ℝ)
    (q : Ch02.MultiscaleExponent) :
    unitCubeLambda s q
        (perturbCoeffOn (cubeDomain (originCube d 0))
          (unitRescaledCutoffCoeff M Q n omega)
          (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn 1) =
      unitCubeLambda s q (unitRescaledCutoffCoeff M Q L omega) :=
  Algsuperdiff.Section24.Sensitivity.Provider.Lambda.unitCubeLambda_eq_of_aeeq s q
    (perturbCoeffOn_unitRescaledCutoffCoeff_aeEq M Q hnL omega)

end

end Algsuperdiff.Section3.Provider.BadEvents
