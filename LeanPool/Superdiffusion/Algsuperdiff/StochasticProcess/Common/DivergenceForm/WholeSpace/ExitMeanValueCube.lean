/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueDecomposition
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDEProcess

/-!
# ExitMeanValueCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The datum and the path resolvent of an exhaustion cube

The resolvent decomposition at the first exit from an exhaustion cube involves two resolvents of
the whole-space process: the one killed on leaving the cube, and the whole-space one read at the
exit position.  This file supplies the analytic side of the first and settles the second for a
nonnegative continuous datum vanishing at infinity.

* `lintegral_pathResolvent_c0`: the expected discounted occupation of the datum along the paths
  of the compactified process is the zero extension of the analytic resolvent supplied with the
  process.  At the added point both sides vanish, because that point is absorbing and the
  observable vanishes there.

Both statements are on the one-point compactification, where the process lives.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

variable [NeZero d]

/-! ## The whole-space resolvent along the paths -/

omit [NeZero d] in
/-- The kernel resolvent of the compactified process vanishes at the added point on an observable
that vanishes there: the point is absorbing. -/
theorem kernelResolvent_onePointLiveExtension_infty
    (R : PositiveC0ContractiveResolvent (Vec d)) (lam : ℝ) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) :
    R.onePointKernelSemigroup.kernelResolvent lam
      (PositiveC0ContractiveResolvent.onePointLiveExtension f) OnePoint.infty = 0 := by
  rw [SubMarkovKernelSemigroup.kernelResolvent]
  have hinner : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-lam * t)) *
      (∫⁻ y, PositiveC0ContractiveResolvent.onePointLiveExtension f y
        ∂(R.onePointKernelSemigroup (Real.toNNReal t) OnePoint.infty)) = 0 := by
    intro t
    rw [R.onePointKernelSemigroup_absorbing,
      lintegral_dirac' _ (PositiveC0ContractiveResolvent.measurable_onePointLiveExtension hf),
      PositiveC0ContractiveResolvent.onePointLiveExtension_infty, mul_zero]
  simp only [hinner]
  exact lintegral_zero

omit [NeZero d] in
/-- **The expected discounted occupation of a continuous datum.**  Along the paths of the
compactified process the expected discounted occupation of the zero extension of a nonnegative
continuous datum vanishing at infinity is the zero extension of the analytic resolvent supplied
with the process. -/
theorem lintegral_pathResolvent_c0 (R : PositiveC0ContractiveResolvent (Vec d))
    (hreg : R.OnePointRegular) (lam : PositiveShift) (g : C₀(Vec d, ℝ))
    (hg0 : ∀ y, 0 ≤ g y) (z : OnePoint (Vec d)) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    (∫⁻ omega, ContinuousPath.pathResolvent (lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y ↦ ENNReal.ofReal (g y))) omega
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup z)) =
      PositiveC0ContractiveResolvent.onePointLiveExtension
        (fun y ↦ ENNReal.ofReal (R.toContractiveResolvent.operator lam g y)) z := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  have hmeas : Measurable fun y : Vec d ↦ ENNReal.ofReal (g y) :=
    ENNReal.measurable_ofReal.comp g.continuous.measurable
  have hlive : Measurable (PositiveC0ContractiveResolvent.onePointLiveExtension
      (fun y ↦ ENNReal.ofReal (g y))) :=
    PositiveC0ContractiveResolvent.measurable_onePointLiveExtension hmeas
  have hstep : (∫⁻ omega, ContinuousPath.pathResolvent (lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y ↦ ENNReal.ofReal (g y))) omega
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup z)) =
      R.onePointKernelSemigroup.kernelResolvent (lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y ↦ ENNReal.ofReal (g y))) z := by
    rw [IsConservative.lintegral_pathResolvent_eq_killedResolvent_univ
      R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup (lam : ℝ) hlive z,
      R.isFellerKernelSemigroup_onePointKernelSemigroup.kernelResolvent_eq_killedResolvent_univ
        R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
        hreg.kolmogorovRegular (lam : ℝ) hlive z]
  have hfinal : (∫⁻ omega, ContinuousPath.pathResolvent (lam : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y ↦ ENNReal.ofReal (g y))) omega
        ∂(IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup z)) =
      PositiveC0ContractiveResolvent.onePointLiveExtension
        (fun y ↦ ENNReal.ofReal (R.toContractiveResolvent.operator lam g y)) z := by
    rw [hstep]
    induction z using OnePoint.rec with
    | infty =>
      rw [kernelResolvent_onePointLiveExtension_infty R (lam : ℝ) hmeas,
        PositiveC0ContractiveResolvent.onePointLiveExtension_infty]
    | coe y =>
      rw [onePointKernelResolvent_liveExtension_eq R (lam : ℝ) hmeas y,
        PositiveC0ContractiveResolvent.kernelResolvent_ofReal_eq_operator R lam g hg0 y,
        PositiveC0ContractiveResolvent.onePointLiveExtension_coe]
  exact hfinal

end

end DivergenceFormProcess.Form
