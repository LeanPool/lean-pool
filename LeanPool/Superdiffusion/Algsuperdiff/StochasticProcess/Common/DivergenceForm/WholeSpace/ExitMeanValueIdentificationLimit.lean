/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueIdentificationCarrier

/-!
# ExitMeanValueIdentificationLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The vanishing-shift limit of the zero-trace solutions on an exhaustion cube

The Dirichlet resolvent of a bounded measurable datum on an exhaustion cube is the value
component of a zero-trace carrier element, the solution of the shifted weak equation.  This file
shows that this carrier element converges as the shift decreases to zero, and identifies the
value component of the limit with the Green potential of `ExitMeanValueHarmonicPotential.lean`.

The convergence is a genuine energy estimate, not a compactness argument.  Subtracting the weak
equations at two shifts and testing against the difference gives

  `nu * ‖grad (Z_s - Z_t)‖² ≤ t ⟪Z_t, Z_s - Z_t⟫ - s ⟪Z_s, Z_s - Z_t⟫`,

whose right-hand side is at most `(s + t)` times a constant, because the shift-uniform
supremum bound of the Dirichlet resolvents bounds every `Z_lam` in `L²` uniformly in the shift.
The Poincare inequality on the carrier converts the gradient estimate into a carrier-norm
estimate, so the family is Cauchy as the shift decreases to zero and the carrier is complete.

The limit solves the *unshifted* weak equation, because the term carrying the shift vanishes.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open ZeroTraceSobolev
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The shift-indexed family on the carrier -/

/-- The `L²` class of a bounded measurable datum on an exhaustion cube. -/
def cubeDatumL2 (v : ℕ) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) : ScalarL2 (wholeSpaceCube d v) :=
  boundedMeasurableToScalarL2 (isOpenBoundedConvexDomain_wholeSpaceCube d v)
    (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)

end

end DivergenceFormProcess.Form
