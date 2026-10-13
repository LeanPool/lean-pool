/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Main
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointConservative
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ResolventTail
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.ConservativeResolvent

/-!
# Process

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The whole-space continuous process from resolvent tails

This module constructs the continuous process from an explicit resolvent-tail
input.  The main construction uses the exhaustion metric on the one-point
compactification.  It therefore accepts the localized split-skew route for
coefficients `a = nu I + ks + kl` with logarithmic local bounds and a finite
cubic layer-cake tail budget.  Conservativity shows that a
process started in the whole space almost surely never reaches the added
point.

The construction is generic over the exhaustion function and tail profile.
The scale-free small-contrast tail supplies the first analytic instance; the
localized split-skew tail can replace it without changing the process API.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory ProbabilityTheory Set
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The canonical process on a one-point regularity witness.** -/
def onePointProcess {R : PositiveC0ContractiveResolvent (Vec d)}
    (hreg : R.OnePointRegular) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    Kernel (OnePoint (Vec d)) (ContinuousPath (OnePoint (Vec d))) := by
  letI := hreg.metricSpace
  letI := hreg.completeSpace
  exact IsConservative.continuousProcess R.onePointKernelSemigroup
    R.isConservative_onePointKernelSemigroup

omit [NeZero d] in
/-- The canonical process is Markov and has the finite-dimensional
distributions of the represented one-point kernel semigroup. -/
theorem onePointProcess_spec {R : PositiveC0ContractiveResolvent (Vec d)}
    (hreg : R.OnePointRegular) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsMarkovKernel (onePointProcess hreg) ∧
      ∀ I : Finset NNReal,
        (onePointProcess hreg).map (ContinuousPath.finsetEvaluation I) =
          finiteSetKernel R.onePointKernelSemigroup I := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  refine ⟨?_, ?_⟩
  · change IsMarkovKernel
      (IsConservative.continuousProcess R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup)
    infer_instance
  exact (R.isFellerKernelSemigroup_onePointKernelSemigroup
    ).continuousProcess_map_finiteEvaluation R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup hreg.kolmogorovRegular

omit [NeZero d] in
/-- Under live-space conservativity, the canonical process started at a live
point almost surely never reaches the added point. -/
theorem onePointProcess_ae_stays_live
    {R : PositiveC0ContractiveResolvent (Vec d)} (hreg : R.OnePointRegular)
    (hcons : R.kernelSemigroup.IsConservative) (x : Vec d) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    ∀ᵐ omega ∂onePointProcess hreg (x : OnePoint (Vec d)),
      ContinuousPath.exitTime
        (Set.range ((↑) : Vec d → OnePoint (Vec d))) omega = ⊤ := by
  let := hreg.metricSpace
  let := hreg.completeSpace
  exact hreg.ae_exitTime_eq_top one_pos x
    (hcons.ofReal_mul_kernelResolvent_one one_pos x)

namespace WholeSpaceVariableExhaustionResolventTailInput

variable {R : PositiveC0ContractiveResolvent (Vec d)}

/-- The whole-space process supplied by a shift-dependent exhaustion-tail
input. -/
def wholeSpaceProcess (H : WholeSpaceVariableExhaustionResolventTailInput R) :
    let hreg := H.toOnePointRegular
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    Kernel (OnePoint (Vec d)) (ContinuousPath (OnePoint (Vec d))) :=
  onePointProcess H.toOnePointRegular

omit [NeZero d] in
/-- The variable-tail whole-space process is Markov and has the represented
one-point kernel semigroup's finite-dimensional distributions. -/
theorem wholeSpaceProcess_spec
    (H : WholeSpaceVariableExhaustionResolventTailInput R) :
    let hreg := H.toOnePointRegular
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsMarkovKernel H.wholeSpaceProcess ∧
      ∀ I : Finset NNReal,
        H.wholeSpaceProcess.map (ContinuousPath.finsetEvaluation I) =
          finiteSetKernel R.onePointKernelSemigroup I :=
  onePointProcess_spec H.toOnePointRegular

omit [NeZero d] in
/-- Under conservativity, the variable-tail process started at a live point
almost surely never reaches the added point. -/
theorem wholeSpaceProcess_ae_stays_live
    (H : WholeSpaceVariableExhaustionResolventTailInput R)
    (hcons : R.kernelSemigroup.IsConservative) (x : Vec d) :
    let hreg := H.toOnePointRegular
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    ∀ᵐ omega ∂H.wholeSpaceProcess (x : OnePoint (Vec d)),
      ContinuousPath.exitTime
        (Set.range ((↑) : Vec d → OnePoint (Vec d))) omega = ⊤ :=
  onePointProcess_ae_stays_live H.toOnePointRegular hcons x

end WholeSpaceVariableExhaustionResolventTailInput

end

end DivergenceFormProcess.Form
