/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Limit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Minimal

/-!
# CutoffAnalyticData

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The whole-space analytic datum of the coefficient cutoff

The whole-space process is built from a coefficient field of the form `a = ν I + k` with `ν > 0`
and `k` continuous and skew of arbitrary size; that structure is packaged as
`WholeSpaceAnalyticData`.  The coefficient cutoff `a_m = ν I + k_m` of the shell decomposition has
exactly that shape: its symmetric part is `ν I` at every point, by the skewness of every shell,
and each entry of `k_m` is continuous, being a locally uniform limit of finite sums of continuous
shells on the convergent sample carrier.

This file records the resulting whole-space analytic datum, whose coefficient field is
the cutoff field itself.  It carries no small-contrast or ellipticity-upper data: those are
separate structures, supplied where the analytic estimates are run.

## Main definitions


## Main results

* `continuous_coefficientCutoff` — the cutoff field is continuous.
* `cutoffWholeSpaceAnalyticData_a` — its coefficient field is the cutoff field.

## References

* ABK26, the shell decomposition of Section 3 and the whole-space coefficient structure of
  Section 5.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open DivergenceFormProcess.Form
open HCPolySupport

noncomputable section

variable {d : ℕ}

/-- **The coefficient cutoff is a continuous field.**  Each entry of the lower-infinite shell sum
is a locally uniform limit of finite sums of continuous shells on the convergent sample carrier,
so the cutoff field is continuous and, with the constant molecular part added, so is `a_m`. -/
theorem continuous_coefficientCutoff (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    Continuous ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) := by
  have hcut : Continuous fun y : Vec d => Cutoff.cutoff m omega y :=
    continuous_pi fun i => continuous_pi fun j => Cutoff.continuous_cutoff_entry m omega i j
  have hconst : Continuous fun _ : Vec d => M.nu • (1 : Mat d) := continuous_const
  refine (hconst.add hcut).congr fun y => ?_
  rw [HCPolySupport.RegCoeffField.toCoeffField_apply, Cutoff.coefficientCutoff_apply]
  rfl

end

end Algsuperdiff.Section5.Provider
