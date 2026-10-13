/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueCubeSetAt
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueHarmonicDensity

/-!
# ExitMeanValueCubeSetAtProcess

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The vanishing-shift harmonic part on a translated triadic cube

The resolvent decomposition at the first exit from a domain and the vanishing-shift limit of its
analytic right-hand side are developed on the centred exhaustion cubes in `ExitMeanValue.lean`.
This file states the corresponding predicate on the translated triadic cube `cubeSetAt y n`, the
carrier the localized Dirichlet problems of the field are posed on.

* `IsCubeSetAtResolventHarmonicPart` names the vanishing-shift limit: a function agreeing with
  `psi = R_mu g` off the cube which, on the cube, is the limit as the shift decreases to zero of
  `psi - R^V_lam g + (mu - lam) R^V_lam psi`.
* `hasExitMeanValueOn_onePointRealExtension_of_forall_approx_cubeSetAt` propagates the exit
  mean-value property of the cube to uniform limits.

The statements are on the one-point compactification, where the process lives.  The analytic
identification of the vanishing-shift limit with the `a`-harmonic extension of the boundary
datum of the cube is a separate question and is not addressed here.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Section5.Support
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)
  (R : PositiveC0ContractiveResolvent (Vec d))
  (hreg : R.OnePointRegular)
  (hcons : R.kernelSemigroup.IsConservative)
  (hid : A.KernelResolventIdentifiesAnalyticMinimal R)

/-! ## 3. The vanishing-shift limit and the exit mean-value property -/

/-- **The vanishing-shift Dirichlet decomposition of a resolvent datum on a translated triadic
cube.**  Write `psi = R_mu g` for the analytic resolvent supplied with the process.  A function
`h` on the live space is the *harmonic part of `psi` on the cube* when it agrees with `psi` off
the cube and, on the cube, is the limit as the shift decreases to zero of
  `psi - R^V_lam g + (mu - lam) R^V_lam psi`,

where `R^V_lam` is the Dirichlet resolvent of the cube.  Only the analytic Dirichlet resolvents
of the cube and the analytic resolvent of the datum appear; no process does. -/
def IsCubeSetAtResolventHarmonicPart (y : Vec d) (n : ℤ) (mu : PositiveShift)
    (g : C₀(Vec d, ℝ)) (h : Vec d → ℝ) : Prop :=
  (∀ z, z ∉ cubeSetAt y n → h z = R.toContractiveResolvent.operator mu g z) ∧
    ∀ z ∈ cubeSetAt y n,
      Tendsto (fun lam : ℝ => R.toContractiveResolvent.operator mu g z -
          A.cubeSetAtC0Resolvent y n g lam z +
          ((mu : ℝ) - lam) *
            A.cubeSetAtC0Resolvent y n (R.toContractiveResolvent.operator mu g) lam z)
        (𝓝[>] (0 : ℝ)) (𝓝 (h z))

end WholeSpaceAnalyticData

omit [NeZero d] in
/-- **The exit mean-value property of a translated triadic cube passes to uniform limits of the
boundary data.**  This is the process side of a density argument: a uniform limit of zero
extensions with the exit mean-value property has it too. -/
theorem hasExitMeanValueOn_onePointRealExtension_of_forall_approx_cubeSetAt
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : R.OnePointRegular) (y : Vec d) (n : ℤ)
    {h : Vec d → ℝ} (hh : Measurable h) {M : ℝ} (hM : ∀ z, |h z| ≤ M)
    (happrox : letI := hreg.metricSpace
      letI := hreg.completeSpace
      ∀ eps > (0 : ℝ), ∃ k : Vec d → ℝ, Measurable k ∧ (∃ C : ℝ, ∀ z, |k z| ≤ C) ∧
        HasExitMeanValueOn R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
          (onePointRealExtension k) ∧ ∀ z, |k z - h z| ≤ eps) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    HasExitMeanValueOn R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n)
      (onePointRealExtension h) := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  have hM0 : 0 ≤ M := (abs_nonneg (h 0)).trans (hM 0)
  refine hasExitMeanValueOn_of_forall_approx R.onePointKernelSemigroup
    R.isConservative_onePointKernelSemigroup
    (OnePoint.isOpen_image_coe.mpr (isOpen_cubeSetAt y n))
    (measurable_onePointRealExtension hh) (M := M) (fun z => by
      rw [Real.norm_eq_abs]
      exact abs_onePointRealExtension_le hM0 hM z) ?_
  intro eps heps
  obtain ⟨k, hk, ⟨C, hC⟩, hkharm, hkh⟩ := happrox eps heps
  have hC0 : 0 ≤ C := (abs_nonneg (k 0)).trans (hC 0)
  refine ⟨onePointRealExtension k, measurable_onePointRealExtension hk,
    ⟨C, fun z => ?_⟩, hkharm, fun z => ?_⟩
  · rw [Real.norm_eq_abs]
    exact abs_onePointRealExtension_le hC0 hC z
  · rw [Real.norm_eq_abs]
    induction z using OnePoint.rec with
    | infty =>
      rw [onePointRealExtension_infty, onePointRealExtension_infty, sub_self, abs_zero]
      exact heps.le
    | coe w =>
      rw [onePointRealExtension_coe, onePointRealExtension_coe]
      exact hkh w

end

end DivergenceFormProcess.Form
