/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMomentsCubeMeanValue
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CubeSetAtMeanValueStream

/-!
# StoppedMomentsCubeStream

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The stopped moments on a triadic cube for the stream field

The bounds of `StoppedMomentsCubeMeanValue.lean` carry two premises about the process: the exit
mean-value property of the observable on the cube, and the finiteness of the expected exit time
from its centre.  Against the stream field of the model both are supplied: the first by the
consumer lemma of `CubeSetAtMeanValueStream.lean`, from the weak harmonicity of the observable on
the cube and its smooth compactly supported boundary datum; the second by
`expectedExitTime_cubeSetAt_ne_top_stream`.

This file composes the two halves.  No global small-contrast datum appears in any statement: the
process hypotheses are exactly those of the coefficient-generic comparison, namely the resolvent
carrying the process, its one-point regularity data, conservativity of the live kernel semigroup,
the bounded-measurable identification of the kernel resolvent with the analytic minimal resolvent,
and the operator identification against the `C₀` barrier resolvent of the stream field.

The remaining hypotheses are the homogenization inputs: the observable is an `H¹` function of the
cube solving the homogeneous equation weakly there, is continuous there, agrees off the cube with
a smooth compactly supported function, and has that function's trace; and the second observable
is uniformly close to it.

## Main results

* `sq_integral_eval_exitTimeTrunc_onePointRealExtension_le_cubeSetAt_stream` — the square of
  the stopped mean on a triadic cube.
* `abs_integral_eval_exitTimeTrunc_onePointRealExtension_sub_mul_le_cubeSetAt_stream` — the
  stopped second moment on a triadic cube.

## References

* ABK26, Steps 1 and 3 of the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open HCPolySupport MeasureTheory
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.Holder
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open DivergenceFormProcess.Form DivergenceFormProcess.StoppedDirichlet
open DivergenceFormProcess.Form.WholeSpaceAnalyticData
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

section Stream

variable {Model : ABKModel d} {omega : FullSample d Model.gamma}
  (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)
  (hcons : R.kernelSemigroup.IsConservative)
  (hid : (streamWholeSpaceAnalyticData Model omega).KernelResolventIdentifiesAnalyticMinimal R)
  (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
    R.toContractiveResolvent.operator mu g =
      ((streamWholeSpaceC0BarrierData Model omega).resolvent).toContractiveResolvent.operator mu g)

/-! ## 2. The composed stopped mean on a triadic cube -/

include hcons hid hT in
/-- **The squared stopped mean against the stream-field process on a triadic cube.** -/
theorem sq_integral_eval_exitTimeTrunc_onePointRealExtension_le_cubeSetAt_stream
    (y : Vec d) (n : ℤ) {bd : Vec d → ℝ} (hbd : ContDiff ℝ (⊤ : ℕ∞) bd)
    (hbdCompact : HasCompactSupport bd)
    {u : Vec d → ℝ} (hu : Measurable u) {N : ℝ} (hN : ∀ z, |u z| ≤ N)
    (hoff : ∀ z, z ∉ cubeSetAt y n → u z = bd z)
    (hucont : ContinuousOn u (cubeSetAt y n))
    (Y : H1Function (cubeSetAt y n)) (hY : ∀ z, Y.toFun z = u z)
    (hharm : IsScalarForcedWeakSolution (streamWholeSpaceAnalyticData Model omega).a
      (cubeSetAt y n) (fun _ ↦ (0 : ℝ)) Y)
    (htrace : MemH10 (cubeSetAt y n) fun z ↦ u z - bd z)
    {b : Vec d → ℝ} (hb : Measurable b) {K : ℝ} (hK0 : 0 ≤ K)
    (hKb : ∀ z, |b z - u z| ≤ K) (hb0 : b y = 0) (t : NNReal) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    (∫ omegaPath, onePointRealExtension b (omegaPath (ContinuousPath.exitTimeTrunc
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t omegaPath))
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (y : OnePoint (Vec d))))
      ^ (2 : ℕ) ≤ 4 * K ^ (2 : ℕ) := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  have hmean :=
    hasExitMeanValueOn_onePointRealExtension_of_contDiffBoundaryDatum_cubeSetAt_stream R hreg
    hcons hid hT y n hbd hbdCompact hu hN hoff hucont Y hY hharm htrace
  have hwfin := expectedExitTime_cubeSetAt_ne_top_stream R hreg hcons hid hT y n
    (mem_cubeSetAt_self y n)
  exact sq_integral_eval_exitTimeTrunc_onePointRealExtension_le_cubeSetAt_of_hwfin R hreg y n
    hu hN hmean hwfin hb hK0 hKb hb0 t

/-! ## 3. The composed stopped second moment on a triadic cube -/

include hcons hid hT in
/-- **The stopped second moment against the stream-field process on a triadic cube.**  The
corrected observable is the weakly harmonic function less `sigma` times the expected exit time
from the cube. -/
theorem abs_integral_eval_exitTimeTrunc_onePointRealExtension_sub_mul_le_cubeSetAt_stream
    (y : Vec d) (n : ℤ) {bd : Vec d → ℝ} (hbd : ContDiff ℝ (⊤ : ℕ∞) bd)
    (hbdCompact : HasCompactSupport bd)
    {w : Vec d → ℝ} (hwmeas : Measurable w) {N : ℝ} (hN : ∀ z, |w z| ≤ N)
    (hoff : ∀ z, z ∉ cubeSetAt y n → w z = bd z)
    (hwcont : ContinuousOn w (cubeSetAt y n))
    (Y : H1Function (cubeSetAt y n)) (hY : ∀ z, Y.toFun z = w z)
    (hharm : IsScalarForcedWeakSolution (streamWholeSpaceAnalyticData Model omega).a
      (cubeSetAt y n) (fun _ ↦ (0 : ℝ)) Y)
    (htrace : MemH10 (cubeSetAt y n) fun z ↦ w z - bd z)
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
    |(∫ omegaPath, onePointRealExtension q (omegaPath (ContinuousPath.exitTimeTrunc
            (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t omegaPath))
          ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
            R.isConservative_onePointKernelSemigroup (y : OnePoint (Vec d)))) -
        sigma * (t : ℝ)| ≤
      2 * K + sigma * ((t : ℝ) *
        (IsConservative.continuousProcess R.onePointKernelSemigroup
            R.isConservative_onePointKernelSemigroup (y : OnePoint (Vec d))
          (survivalEvent (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t)ᶜ).toReal) := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  have hmean :=
    hasExitMeanValueOn_onePointRealExtension_of_contDiffBoundaryDatum_cubeSetAt_stream R hreg
    hcons hid hT y n hbd hbdCompact hwmeas hN hoff hwcont Y hY hharm htrace
  have hwfin := expectedExitTime_cubeSetAt_ne_top_stream R hreg hcons hid hT y n
    (mem_cubeSetAt_self y n)
  exact abs_integral_eval_exitTimeTrunc_onePointRealExtension_sub_mul_le_cubeSetAt_of_hwfin R
    hreg y n hwmeas hN hmean hwfin hq hCq hsigma hKb hq0 t

end Stream

end

end Algsuperdiff.Section5.Provider
