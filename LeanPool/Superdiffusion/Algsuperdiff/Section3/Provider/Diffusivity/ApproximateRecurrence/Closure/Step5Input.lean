/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5InputSideConditions

/-!
# Step5Input

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `Closure.ClosureStep5Input`, from one remaining binder

`Closure.Step5Basket.step5GaugeEndpoint_closureFamilies_of_momentLegs` reduces
`Closure.Step5GaugeEndpoint` at the closure's own corrector families to ten
binders.  Nine of them are discharged by this lane:

| binder | discharged by |
|---|---|
| `hgate` | `Closure.Step5Basket.step5CrossDefectConst_mul_gamma_pow_fifteen_le_two_of_regime`, from
`ClosureRegime` |
| `hshell` |
`Closure.Step5InputShellMoment.gridFourthMoment_matrixOperatorNorm_freshShellCubeAverage_root_le` |
| `hAmem` | `Closure.Step5InputShellMoment.memLp_four_matrixOperatorNorm_freshShellCubeAverage` |
| `hgradM`, `hvmem` | `Closure.Step5InputGradMoment.exists_step5GradMomentConst` |
| `hmemOsc`, `hosc` | `Closure.Step5InputOscillation.exists_gamma0_step5OscillationLegs` |
| `hmeasX`, `hmeasS` | `Closure.Step5InputSideConditions.aestronglyMeasurable_step5PairingX`/`S` |
| `hintP` |
`Closure.Step5InputSideConditions.integrableOn_cubeSet_vecDot_matVecMul_finiteShellIncrement` |

The tenth, `hsampDef`, is carried here as an explicit binder of
`closureStep5Input_of_sampDef`; see the disclosure.

## The regime arithmetic

Three thresholds are merged into the single produced constant:

* `step5GateConst d` --- the Step-5 defect gate `Cdef cgamma^15 <= 2`;
* `closureRegimeConst` --- kept so that a caller reading this input at the
  closure's own threshold never needs a second enlargement;
* `ClosureRegime` gives `C c⋆^{-1} <= E` and `cgamma <= E^{-5}`, hence `cgamma
  <= E^{-1} <= (2C/3)^{-1}`, so `C >= (3/2) gamma0^{-1}` forces `cgamma <=
  gamma0`.

No smallness of the manuscript is assumed: every threshold is *produced*, and
each is consumed only inside `Closure.ClosureRegime`.

The localization scale is taken large in three ways at once --- the mesh-depth
identity `K - j = nmesh` of `Closure.ClosureAssembly.eventually_closureMeshDepth_scale`,
the recurrence-parameter gate `10^10 cgamma^{-1} <= K - (n+h)` and `n + h <= K` ---
all three being `Filter.atTop` conditions on `K`, which is exactly the form
`Closure.ClosureStep5Input` reads.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 5; `e.km.kn.Lp`;
  `e.nablaw.in.L.eight`; `e.lower.bound.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The mesh scale the closure names is at most the base scale: it is
`n + h - h - gap`. -/
theorem recurrenceMesoScale_closure_le (M : ABKModel d) (n : ℤ) (h : ℕ) :
    recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ) ≤ n := by
  have hbase := recurrenceMesoScale_le recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ)
  omega

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
