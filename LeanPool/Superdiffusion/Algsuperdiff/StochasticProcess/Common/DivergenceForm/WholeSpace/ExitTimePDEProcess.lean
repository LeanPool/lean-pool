/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxLowerProcess
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CruxUpperProcess
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDE
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.KernelIdentification
public import LeanPool.MarkovProcess.MarkovProcess.Killed.ExitTimeIdentification

/-!
# ExitTimePDEProcess

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The expected exit time from an exhaustion cube

The expected time the whole-space process spends in a bounded domain before
leaving it is the value at the starting point of the Dirichlet problem with
constant forcing on that domain.  This file proves that identity for the
exhaustion cubes.

The two inputs are already available.  The identification of the killed
resolvent with the Dirichlet resolvent of the part domain holds at every
positive shift and is carried here with its own hypotheses; instantiated at
the constant datum it is exactly the identification binder of the
expected-exit-time theorem, once the observable is replaced by the constant
one, which is legitimate because the killed kernels put no mass outside the
part domain (`killedResolvent_congr_of_eqOn`).  The limit binder is supplied
by the analytic layer: the Dirichlet resolvents of the constant datum increase
as the shift decreases, and their supremum along the shifts `1 / (n + 1)` is
`cubeExitFunction`.

Two one-sided forms follow, an upper bound from a uniform upper bound for the
limit on the cube and a lower bound on a subset from a uniform lower bound
there; the second is also recorded in the concrete form in which a single
positive shift already bounds the expected exit time from below.

The statements are about the process on the one-point compactification and the
exit time from the image of the cube there.  Reading them on ordinary
trajectories of the live space is a separate step and is not taken here.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

/-- **The killed resolvent only reads the observable on the part domain.**
The killed kernels put no mass outside it, so two observables agreeing there
have the same killed resolvent. -/
theorem killedResolvent_congr_of_eqOn {alpha : Type*} [MetricSpace alpha]
    [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
    [SecondCountableTopology alpha] [Nonempty alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (U : Set alpha) (hU : IsOpen U) (lam : ℝ) {f g : alpha → ℝ≥0∞}
    (h : ∀ y ∈ U, f y = g y) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x =
      IsConservative.killedResolvent P hP U hU lam g x := by
  unfold IsConservative.killedResolvent
  refine lintegral_congr fun t => ?_
  refine congrArg _ (lintegral_congr_ae ?_)
  filter_upwards [IsConservative.ae_mem_killedKernel P hP U hU (Real.toNNReal t) x]
    with y hy
  exact h y hy

variable {d : ℕ}

variable [NeZero d]

namespace WholeSpaceAnalyticData

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
