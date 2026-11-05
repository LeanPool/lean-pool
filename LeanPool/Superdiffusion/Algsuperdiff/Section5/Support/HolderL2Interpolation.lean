/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CubeCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderGauge

/-!
# HolderL2Interpolation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Square integrability from continuity and a Hölder bound

A continuous function with a finite Hölder bound on a bounded cube has a
uniform pointwise bound there, hence belongs to `L²` on the cube.

## References

* ABK26, the localized error and regularity quantities of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Square integrability -/

theorem memLp_two_of_continuousOn_of_holder {y : Vec d} {n : ℤ} {K : ℝ} (hK : 0 ≤ K)
    {f : Vec d → ℝ} (hcont : ContinuousOn f (cubeSetAt y n))
    (hf : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K f) :
    MemLp f 2 (volume.restrict (cubeSetAt y n)) := by
  have : IsFiniteMeasure (volumeMeasureOn (cubeSetAt y n)) :=
    (isOpenBoundedConvexDomain_cubeSetAt y n).isFiniteMeasure_restrict_volume
  refine MemLp.of_bound (hcont.aestronglyMeasurable (measurableSet_cubeSetAt y n))
    (|f y| + K * ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ)) ?_
  refine (ae_restrict_iff' (measurableSet_cubeSetAt y n)).2
    (Filter.Eventually.of_forall fun x hx => ?_)
  have hy := mem_cubeSetAt_self y n
  have hbd := hf x hx y hy
  have hdiam : ‖x - y‖ ≤ (3 : ℝ) ^ n := (norm_sub_lt_of_mem_cubeSetAt hx hy).le
  have hmono : ‖x - y‖ ^ (1 / 2 : ℝ) ≤ ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) hdiam (by norm_num)
  have htri : ‖f x‖ ≤ ‖f x - f y‖ + ‖f y‖ := by
    simpa using norm_add_le (f x - f y) (f y)
  have hKmono := mul_le_mul_of_nonneg_left hmono hK
  simp only [Real.norm_eq_abs] at htri hbd ⊢
  linarith [hbd, hKmono, htri]

end

end Algsuperdiff.Section5.Support
