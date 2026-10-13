/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.TailGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.TailSummability
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Summability

/-!
# TailMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# First moments of the two tail gauges

The two legs of the quantitative tail condition of `TailGauge.lean` are
controlled in the mean by the two proved shell displays of the assumptions:

* the descending value gauge `‖j_{ℓ-r}‖_{L^∞(□_ℓ)}` has the one-shell scaling
  law of `(J2)`, whose first moment on the cube `□_ℓ` is of order
  `3^{γ(ℓ-r)} (1+r)^{1/2}`, the profile `cubeMajorant`;
* the ascending volume-normalized gradient gauge
  `‖∇ j_{ℓ+r}‖_{W^{1,∞}(y+□_ℓ)}` has a `Γ₂` upper tail at the amplitude
  `3^{-ℓ} 3^{(γ-1)(ℓ+r)}` of `e.nabla.jk.O`, so its first moment is at most a
  constant multiple of that amplitude.

Weighing the first by `3^{-ℓ}` and the second by `3^{ℓ}` makes both profiles
proportional to `(3^{γ-1})^{ℓ}`, which is summable because `γ ≤ 1/4`.

## References

* ABK26, `e.jk.O`, `e.nabla.jk.O`.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 3. The ascending gradient leg -/

theorem measurable_shellW1InfGradNorm_translate_comp (k i : ℤ) (y : Vec d) :
    Measurable fun omega : CutoffSample d =>
      Section4.Support.shellW1InfGradNorm k (ShellField.translate y (omega.1 i)) :=
  (Section4.Support.measurable_shellW1InfGradNorm k).comp
    ((ShellField.measurable_translate y).comp
      ((measurable_pi_apply i).comp measurable_subtype_coe))

/-- Positivity of the ascending amplitude. -/
theorem shellW1InfGradAmplitude_pos (M : ABKModel d) (k i : ℤ) :
    0 < (3 : ℝ) ^ (-k) * Real.rpow 3 ((M.gamma - 1) * (i : ℝ)) :=
  mul_pos (zpow_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)

end

end Algsuperdiff.Section5.Field
