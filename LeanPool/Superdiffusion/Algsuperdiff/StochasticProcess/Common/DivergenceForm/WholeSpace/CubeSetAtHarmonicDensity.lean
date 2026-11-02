/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.CubeSetAtHarmonicPart

/-!
# CubeSetAtHarmonicDensity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The uniform bound of the harmonic parts on a translated triadic cube

The harmonic parts of `CubeSetAtHarmonicPart.lean` are attached to nonnegative continuous data
vanishing at infinity, because the exit decomposition is an extended-real statement.  A general
datum is a difference of two nonnegative ones, so this file records the uniform bound the
harmonic parts obey on a translated triadic cube, which is what a difference argument consumes.

`cubeSetAtHarmonicPartBound` is that bound; it is nonnegative and dominates the harmonic part of
the cube everywhere.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Section5.Support
open MarkovProcess MarkovProcess.Semigroup
open DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d) (R : PositiveC0ContractiveResolvent (Vec d))
  (hreg : R.OnePointRegular)
  (hcons : R.kernelSemigroup.IsConservative)
  (hid : A.KernelResolventIdentifiesAnalyticMinimal R)

/-- The uniform bound of a harmonic part on a translated triadic cube. -/
def cubeSetAtHarmonicPartBound (y : Vec d) (n : ℤ) (mu : PositiveShift) (g : C₀(Vec d, ℝ)) :
    ℝ :=
  ‖R.toContractiveResolvent.operator mu g‖ +
    cubeResolventResidualBound R mu g *
      A.partTorsionBound (isOpenBoundedConvexDomain_cubeSetAt y n)

theorem abs_cubeSetAtHarmonicPart_le' (y : Vec d) (n : ℤ) (mu : PositiveShift)
    (g : C₀(Vec d, ℝ)) (z : Vec d) :
    |A.cubeSetAtHarmonicPart R y n mu g z| ≤ A.cubeSetAtHarmonicPartBound R y n mu g :=
  A.abs_cubeSetAtHarmonicPart_le R y n mu g z

theorem cubeSetAtHarmonicPartBound_nonneg (y : Vec d) (n : ℤ) (mu : PositiveShift)
    (g : C₀(Vec d, ℝ)) : 0 ≤ A.cubeSetAtHarmonicPartBound R y n mu g :=
  (abs_nonneg _).trans (A.abs_cubeSetAtHarmonicPart_le' R y n mu g 0)

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
