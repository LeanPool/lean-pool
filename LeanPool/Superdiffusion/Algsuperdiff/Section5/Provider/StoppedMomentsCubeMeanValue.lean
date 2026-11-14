/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMomentsCube

/-!
# StoppedMomentsCubeMeanValue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The stopped moments on a triadic cube with the expected exit time carried

The composed bounds of `StoppedMomentsCube.lean` discharge the finiteness of the expected exit
time from the cube through the small-contrast route, and therefore carry a global small-contrast
datum in every hypothesis list.  The finiteness is the only place that datum is used.

This file restates the same three bounds with the finiteness carried as an explicit binder, at
the one point where it is consumed — the centre of the cube, which is the starting point of the
process.  No analytic datum of the coefficient field appears: the statements below assume only
the resolvent carrying the process and its one-point regularity data.  Every route that supplies
the finiteness — the small-contrast one of `expectedExitTime_cubeSetAt_ne_top` and the
coefficient-generic one of `expectedExitTime_cubeSetAt_ne_top_stream` — instantiates them.

## Main results

* `abs_integral_eval_exitTimeTrunc_onePointRealExtension_le_cubeSetAt_of_hwfin` — the stopped
  mean.
* `sq_integral_eval_exitTimeTrunc_onePointRealExtension_le_cubeSetAt_of_hwfin` — its square.
* `abs_integral_eval_exitTimeTrunc_onePointRealExtension_sub_mul_le_cubeSetAt_of_hwfin` — the
  stopped second moment.

## References

* ABK26, Steps 1 and 3 of the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Provider.Holder
open Algsuperdiff.Section5.Support
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open DivergenceFormProcess.Form DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

section CarriedExitTime

variable (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)

/-! ## 1. The stopped mean -/

/-- **The stopped mean against the whole-space process on a triadic cube, with the expected exit
time carried.**  A bounded Borel observable vanishing at the centre has stopped mean at most twice
its uniform distance to an observable with the exit mean-value property of the cube. -/
theorem abs_integral_eval_exitTimeTrunc_onePointRealExtension_le_cubeSetAt_of_hwfin
    (y : Vec d) (n : ℤ) {u : Vec d → ℝ} (hu : Measurable u) {M : ℝ} (hM : ∀ z, |u z| ≤ M)
    (hmean : letI := hreg.metricSpace
      letI := hreg.completeSpace
      HasExitMeanValueOn R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) (onePointRealExtension u))
    (hwfin : letI := hreg.metricSpace
      letI := hreg.completeSpace
      expectedExitTime R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) (y : OnePoint (Vec d)) ≠ ⊤)
    {b : Vec d → ℝ} (hb : Measurable b) {K : ℝ} (hK0 : 0 ≤ K)
    (hKb : ∀ z, |b z - u z| ≤ K) (hb0 : b y = 0) (t : NNReal) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    |∫ omega, onePointRealExtension b (omega (ContinuousPath.exitTimeTrunc
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t omega))
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (y : OnePoint (Vec d)))| ≤
      2 * K := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (u y)) (hM y)
  have hcentre : y ∈ cubeSetAt y n := mem_cubeSetAt_self y n
  refine abs_integral_eval_exitTimeTrunc_le_of_hasExitMeanValueOn
    R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
    R.isFellerKernelSemigroup_onePointKernelSemigroup hreg.kolmogorovRegular
    (isOpen_image_coe_of_isOpen (isOpen_cubeSetAt y n))
    (measurable_onePointRealExtension hu)
    (abs_onePointRealExtension_le hM0 hM) hmean
    (measurable_onePointRealExtension hb) ?_ t
    (Set.mem_image_of_mem _ hcentre) ?_ hwfin
  · intro z
    induction z using OnePoint.rec with
    | infty => simpa using hK0
    | coe w => simpa using hKb w
  · simpa using hb0

/-- **The squared stopped mean on a triadic cube, with the expected exit time carried.** -/
theorem sq_integral_eval_exitTimeTrunc_onePointRealExtension_le_cubeSetAt_of_hwfin
    (y : Vec d) (n : ℤ) {u : Vec d → ℝ} (hu : Measurable u) {M : ℝ} (hM : ∀ z, |u z| ≤ M)
    (hmean : letI := hreg.metricSpace
      letI := hreg.completeSpace
      HasExitMeanValueOn R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) (onePointRealExtension u))
    (hwfin : letI := hreg.metricSpace
      letI := hreg.completeSpace
      expectedExitTime R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) (y : OnePoint (Vec d)) ≠ ⊤)
    {b : Vec d → ℝ} (hb : Measurable b) {K : ℝ} (hK0 : 0 ≤ K)
    (hKb : ∀ z, |b z - u z| ≤ K) (hb0 : b y = 0) (t : NNReal) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    (∫ omega, onePointRealExtension b (omega (ContinuousPath.exitTimeTrunc
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t omega))
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (y : OnePoint (Vec d))))
      ^ (2 : ℕ) ≤ 4 * K ^ (2 : ℕ) := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  have hbase := abs_integral_eval_exitTimeTrunc_onePointRealExtension_le_cubeSetAt_of_hwfin
    R hreg y n hu hM hmean hwfin hb hK0 hKb hb0 t
  calc (∫ omega, onePointRealExtension b (omega (ContinuousPath.exitTimeTrunc
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t omega))
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (y : OnePoint (Vec d))))
        ^ (2 : ℕ)
      = |∫ omega, onePointRealExtension b (omega (ContinuousPath.exitTimeTrunc
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t omega))
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (y : OnePoint (Vec d)))|
        ^ (2 : ℕ) := (sq_abs _).symm
    _ ≤ (2 * K) ^ (2 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hbase 2
    _ = 4 * K ^ (2 : ℕ) := by ring

/-! ## 2. The stopped second moment -/

/-- **The stopped second moment against the whole-space process on a triadic cube, with the
expected exit time carried.** -/
theorem abs_integral_eval_exitTimeTrunc_onePointRealExtension_sub_mul_le_cubeSetAt_of_hwfin
    (y : Vec d) (n : ℤ) {w : Vec d → ℝ} (hwmeas : Measurable w) {M : ℝ}
    (hM : ∀ z, |w z| ≤ M)
    (hmean : letI := hreg.metricSpace
      letI := hreg.completeSpace
      HasExitMeanValueOn R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) (onePointRealExtension w))
    (hwfin : letI := hreg.metricSpace
      letI := hreg.completeSpace
      expectedExitTime R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) (y : OnePoint (Vec d)) ≠ ⊤)
    {q : Vec d → ℝ} (hq : Measurable q) {Cq : ℝ} (hCq : ∀ z, |q z| ≤ Cq)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) {K : ℝ}
    (hKb : letI := hreg.metricSpace
      letI := hreg.completeSpace
      ∀ z : OnePoint (Vec d),
        |onePointRealExtension q z - (onePointRealExtension w z -
          sigma * (expectedExitTime R.onePointKernelSemigroup
            R.isConservative_onePointKernelSemigroup
            (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) z).toReal)| ≤ K)
    (hq0 : q y = 0) (t : NNReal) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    |(∫ omega, onePointRealExtension q (omega (ContinuousPath.exitTimeTrunc
            (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t omega))
          ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
            R.isConservative_onePointKernelSemigroup (y : OnePoint (Vec d)))) -
        sigma * (t : ℝ)| ≤
      2 * K + sigma * ((t : ℝ) *
        (IsConservative.continuousProcess R.onePointKernelSemigroup
            R.isConservative_onePointKernelSemigroup (y : OnePoint (Vec d))
          (survivalEvent (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t)ᶜ).toReal) := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (w y)) (hM y)
  have hCq0 : 0 ≤ Cq := le_trans (abs_nonneg (q y)) (hCq y)
  have hcentre : y ∈ cubeSetAt y n := mem_cubeSetAt_self y n
  refine abs_integral_eval_exitTimeTrunc_sub_mul_le_of_hasExitMeanValueOn
    R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
    R.isFellerKernelSemigroup_onePointKernelSemigroup hreg.kolmogorovRegular
    (isOpen_image_coe_of_isOpen (isOpen_cubeSetAt y n))
    (measurable_onePointRealExtension hwmeas) (abs_onePointRealExtension_le hM0 hM) hmean
    hsigma (fun _ => rfl) (measurable_onePointRealExtension hq)
    (abs_onePointRealExtension_le hCq0 hCq) hKb t (Set.mem_image_of_mem _ hcentre) ?_ hwfin
  simpa using hq0

end CarriedExitTime

end

end Algsuperdiff.Section5.Provider
