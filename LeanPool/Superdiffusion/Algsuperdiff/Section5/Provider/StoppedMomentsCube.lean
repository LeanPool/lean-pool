/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Holder.CubeTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMomentsProcess
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueCubeSetAtProcess

/-!
# StoppedMomentsCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The second moment of the whole displacement on a triadic cube

The stopped second moment of `StoppedMoments.lean` is stated for an abstract conservative
Feller process, an abstract open set and one observable.  This file sums it over the coordinate
directions at the compactified whole-space process of a positive `C₀` contractive resolvent and
at the image of the translated triadic cube `cubeSetAt y n`, the carrier the renormalization
estimate of the generator is read on: coordinate observables each within `B` of `sigma * t` at
the stopped position bound the squared norm observable within `d * B` of `d * sigma * t`.

## Main results

* `abs_integral_eval_exitTimeTrunc_vecNormSq_sub_le_cubeSetAt` — the sum over the coordinate
  directions.

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

variable {d : ℕ} [NeZero d]

section Displacement

variable (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)

omit [NeZero d] in
/-- **The second moment of the whole displacement on a triadic cube.**  Summing the coordinate
observables, each within `B` of `sigma * t` at the stopped position, bounds the squared norm
observable within `d * B` of `d * sigma * t`. -/
theorem abs_integral_eval_exitTimeTrunc_vecNormSq_sub_le_cubeSetAt
    (y : Vec d) (n : ℤ) {c : Vec d → ℝ}
    (hQmeas : ∀ i : Fin d, Measurable fun z => c z * quadraticObservable (basisVec i) z)
    {CQ : ℝ} (hCQ : ∀ (i : Fin d) (z : Vec d),
      |c z * quadraticObservable (basisVec i) z| ≤ CQ)
    {sigma B : ℝ} (t : NNReal)
    (hQ : letI := hreg.metricSpace
      letI := hreg.completeSpace
      ∀ i : Fin d,
        |(∫ omega, onePointRealExtension
              (fun z => c z * quadraticObservable (basisVec i) z)
              (omega (ContinuousPath.exitTimeTrunc
                (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t omega))
            ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
              R.isConservative_onePointKernelSemigroup (y : OnePoint (Vec d)))) -
          sigma * (t : ℝ)| ≤ B) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    |(∫ omega, onePointRealExtension (fun z => c z * vecNormSq z)
            (omega (ContinuousPath.exitTimeTrunc
              (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t omega))
          ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
            R.isConservative_onePointKernelSemigroup (y : OnePoint (Vec d)))) -
        (d : ℝ) * (sigma * (t : ℝ))| ≤ (d : ℝ) * B := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  have hCQ0 : ∀ (i : Fin d) (z : OnePoint (Vec d)),
      |onePointRealExtension (fun w => c w * quadraticObservable (basisVec i) w) z| ≤ CQ := by
    intro i
    refine abs_onePointRealExtension_le ?_ (hCQ i)
    exact le_trans (abs_nonneg _) (hCQ i 0)
  refine abs_integral_sum_eval_exitTimeTrunc_sub_le
    R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup hreg.kolmogorovRegular
    (isOpen_image_coe_of_isOpen (isOpen_cubeSetAt y n))
    (fun i => onePointRealExtension fun z => c z * quadraticObservable (basisVec i) z)
    (onePointRealExtension fun z => c z * vecNormSq z)
    (fun z _ => (onePointRealExtension_sum_quadraticObservable c z).symm)
    (fun i => measurable_onePointRealExtension (hQmeas i)) hCQ0 t
    (Set.mem_image_of_mem _ (mem_cubeSetAt_self y n)) hQ

end Displacement

end

end Algsuperdiff.Section5.Provider
