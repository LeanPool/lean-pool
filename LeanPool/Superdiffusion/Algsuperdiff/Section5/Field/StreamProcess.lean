/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.ExhaustionTailInput
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.WholeSpaceKernelConservativity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamCube
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamExitTime
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxStreamMeanValueIdentification
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Process

/-!
# StreamProcess

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The continuous process of the stream field

This module gives names to the split-skew analytic resolvent, its variable
exhaustion-tail input, and the resulting continuous-path process on the
one-point compactification.  Every object is assembled from the model data;
there is no global small-contrast hypothesis.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form HCPolySupport MeasureTheory
open DivergenceFormProcess.StoppedDirichlet
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open ProbabilityTheory
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The positive contractive `C₀` resolvent assembled from the stream field's
localized split-skew estimates. -/
def streamWholeSpaceResolvent (M : ABKModel d) (omega : FullSample d M.gamma) :
    PositiveC0ContractiveResolvent (Vec d) :=
  streamAnalyticMinimalPositiveC0ContractiveResolvent M omega

/-- The stream resolvent's shift-dependent exhaustion-tail input. -/
def streamExhaustionTailInput (M : ABKModel d) (omega : FullSample d M.gamma) :
    WholeSpaceVariableExhaustionResolventTailInput
      (streamWholeSpaceResolvent M omega) :=
  streamVariableExhaustionTailInput M omega (streamWholeSpaceResolvent M omega)
    (kernelResolventIdentifiesAnalyticMinimal_stream M omega)
    (isConservative_streamKernelSemigroup M omega)

/-- The continuous-path process associated with one realization of the stream
field. -/
def streamProcess (M : ABKModel d) (omega : FullSample d M.gamma) :
    let hreg := (streamExhaustionTailInput M omega).toOnePointRegular
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    Kernel (OnePoint (Vec d)) (ContinuousPath (OnePoint (Vec d))) :=
  (streamExhaustionTailInput M omega).wholeSpaceProcess

/-- A stream process started at a live point almost surely remains in the
whole space for all time. -/
theorem streamProcess_ae_stays_live
    (M : ABKModel d) (omega : FullSample d M.gamma) (x : Vec d) :
    let hreg := (streamExhaustionTailInput M omega).toOnePointRegular
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    ∀ᵐ path ∂streamProcess M omega (x : OnePoint (Vec d)),
      ContinuousPath.exitTime
        (Set.range ((↑) : Vec d → OnePoint (Vec d))) path = ⊤ :=
  (streamExhaustionTailInput M omega).wholeSpaceProcess_ae_stays_live
    (isConservative_streamKernelSemigroup M omega) x

/-! ## Model-level stopped identities -/

end

end Algsuperdiff.Section5.Field
