/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.ScalarWeakMaximumPrinciple
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamGeneralDomain
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueHarmonicDensity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationWhole

/-!
# CruxStreamMeanValueIdentification

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# S-free identification of stream-field exit mean values

This module identifies the analytic harmonic parts used by the S-free stream
mean-value chain and supplies its smooth-boundary consumer.  The declarations
use the stream field's coefficient and `WholeSpaceC0BarrierData`; they do not
assume a global small-contrast datum.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field
open MarkovProcess MarkovProcess.Semigroup
open DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable {M : ABKModel d} {omega : FullSample d M.gamma}
  (R : PositiveC0ContractiveResolvent (Vec d)) (hreg : R.OnePointRegular)
  (hcons : R.kernelSemigroup.IsConservative)
  (hid : (streamWholeSpaceAnalyticData M omega).KernelResolventIdentifiesAnalyticMinimal R)
  (hT : ∀ (mu : PositiveShift) (g : C₀(Vec d, ℝ)),
    R.toContractiveResolvent.operator mu g =
      ((streamWholeSpaceC0BarrierData M omega).resolvent).toContractiveResolvent.operator mu g)

include hT in
/-- The stream process resolvent agrees pointwise with the analytic minimal
resolvent, without a global small-contrast assumption. -/
theorem operator_eq_analyticMinimalResolventReal_stream
    (mu : PositiveShift) (g : C₀(Vec d, ℝ)) (y : Vec d) :
    R.toContractiveResolvent.operator mu g y =
      (streamWholeSpaceAnalyticData M omega).analyticMinimalResolventReal
        mu g g.continuous.measurable (abs_apply_le_norm_zeroAtInfty g) y := by
  rw [hT mu g]
  exact (streamWholeSpaceAnalyticData M omega).analyticMinimalC0ResolventOfVanishing_apply
      (streamWholeSpaceC0BarrierData M omega).vanishing mu g y

end WholeSpaceAnalyticData
end
end DivergenceFormProcess.Form
