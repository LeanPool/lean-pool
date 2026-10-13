/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.ScalarToDivergence
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitTimePDE

/-!
# ExitTimePDETorsion

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The exhaustion cubes of the whole-space exit-time problem

The exit-time problem of a divergence-form operator on a bounded domain `V` is
the unshifted Dirichlet problem

  `-div (a grad w) = 1` in `V`,  `w = 0` on the boundary of `V`,

whose solution is sought in the zero-trace Sobolev space of `V`.  This file
carries the elementary geometry of an exhaustion cube that the construction of
that solution uses, namely that the cube contains the origin, and joins the
scalar-to-divergence conversion to the shifted Dirichlet resolvents.

The solution itself is constructed on every exhaustion cube in
`ExitTimePDEIdentification.lean`, as `cubeTorsionFunction`, and satisfies the
scalar weak equation there
(`cubeTorsionFunction_isScalarForcedWeakSolution`).  The construction goes
through the divergence form of the forcing: the constant one is the divergence
of the vector field with a single nonzero coordinate equal to the
corresponding coordinate function, which is smooth and square integrable on a
bounded domain, so the zero-trace right-hand-side Dirichlet theory applies, and
the pairing lemma of the scalar-to-divergence conversion turns the resulting
identity back into the scalar form
`integral (a grad w) dot grad phi = integral phi`.

That this solution is the limit of the shifted Dirichlet resolvents
`R^V_lam 1` of `ExitTimePDE.lean` as the shift decreases to zero is proved in
`ExitTimePDEIdentificationLimit.lean`, as `cubeExitFunction_coe_eq`, at every
point and for the continuous representative of the torsion function.  The
argument there is not the energy estimate one might expect: the resolvent of
the constant datum is at most the continuous representative of the torsion
function at every point of the cube, and the difference is at most the shift
times the square of the uniform bound of the torsion function, so the
supremum over the shifts is read off from that two-sided squeeze.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

/-- Every exhaustion cube contains the origin, so it is nonempty. -/
theorem wholeSpaceCube_nonempty (d v : ℕ) : (wholeSpaceCube d v).Nonempty := by
  refine ⟨0, mem_wholeSpaceCube_iff.mpr fun i => ?_⟩
  have hpos : (0 : ℝ) < (3 : ℝ) ^ v := by positivity
  exact ⟨by simp [neg_lt_zero.mpr hpos], by simp [hpos]⟩

end

end DivergenceFormProcess.Form
