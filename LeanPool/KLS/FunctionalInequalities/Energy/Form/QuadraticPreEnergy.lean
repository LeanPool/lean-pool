/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Quadratic finite pre-energies

This module records the algebra carried by a concrete finite pre-energy before any closure or
relaxation theorem is used. The test realization is linear, and the finite `NNReal` energy obeys
the quadratic scaling and parallelogram identities.

`PreEnergy.Quadratic` is deliberately weaker than `Energy.ClosedQuadratic`: it does not assert
lower semicontinuity, density, closability, or that relaxation preserves the quadratic identities.
The closure theorem is `Quadratic.closedQuadratic_sequentialRelaxation` in
`Energy.Relaxation.Quadratic`; agreement on tests remains a separate analytic question.
-/

@[expose] public section

namespace FunctionalInequalities.Energy.PreEnergy


universe u v

variable {X : Type u} [AddCommGroup X] [Module ℝ X]
  (P : PreEnergy X) [AddCommGroup P.Test] [Module ℝ P.Test]

/-- A finite pre-energy is quadratic when its realization is linear and its energy satisfies the
finite quadratic identities on the concrete test space.

The scalar factor is written as `‖c‖₊ ^ 2 : NNReal`; over `ℝ` this is exactly `c²`, while keeping
the equality entirely in the finite nonnegative codomain.
-/
structure Quadratic : Prop where
  /-- The zero concrete test realizes the ambient zero vector. -/
  map_zero : P.toAmbient 0 = 0
  /-- Realization preserves addition. -/
  map_add : ∀ f g : P.Test, P.toAmbient (f + g) = P.toAmbient f + P.toAmbient g
  /-- Realization preserves real scalar multiplication. -/
  map_smul : ∀ (c : ℝ) (f : P.Test), P.toAmbient (c • f) = c • P.toAmbient f
  /-- The zero concrete test has zero energy. -/
  energy_zero : P.energy 0 = 0
  /-- Finite energy is homogeneous of degree two. -/
  energy_smul : ∀ (c : ℝ) (f : P.Test),
    P.energy (c • f) = ‖c‖₊ ^ 2 * P.energy f
  /-- The finite parallelogram identity. -/
  parallelogram : ∀ f g : P.Test,
    P.energy (f + g) + P.energy (f - g) = 2 * P.energy f + 2 * P.energy g

namespace Quadratic

variable {P : PreEnergy X} [AddCommGroup P.Test] [Module ℝ P.Test]

/-- The realization of a quadratic pre-energy as a real linear map. -/
def toAmbientₗ (h : P.Quadratic) : P.Test →ₗ[ℝ] X where
  toFun := P.toAmbient
  map_add' := h.map_add
  map_smul' := h.map_smul

/-- The linear realization evaluates to the original realization function. -/
@[simp]
theorem toAmbientₗ_apply (h : P.Quadratic) (f : P.Test) :
    h.toAmbientₗ f = P.toAmbient f :=
  rfl

/-- Realization preserves negation. -/
theorem map_neg (h : P.Quadratic) (f : P.Test) :
    P.toAmbient (-f) = -P.toAmbient f :=
  h.toAmbientₗ.map_neg f

/-- Realization preserves subtraction. -/
theorem map_sub (h : P.Quadratic) (f g : P.Test) :
    P.toAmbient (f - g) = P.toAmbient f - P.toAmbient g :=
  h.toAmbientₗ.map_sub f g

/-- A quadratic finite pre-energy is invariant under negation. -/
@[simp]
theorem energy_neg (h : P.Quadratic) (f : P.Test) : P.energy (-f) = P.energy f := by
  simpa using h.energy_smul (-1) f

variable [TopologicalSpace X]

/-- The sequential relaxation of a quadratic pre-energy vanishes at the ambient zero vector.

This conclusion only uses the constant zero sequence. The remaining quadratic identities for the
relaxation require genuine closure arguments and are not inferred here.
-/
theorem sequentialRelaxation_zero (h : P.Quadratic) : P.sequentialRelaxation 0 = 0 := by
  apply le_antisymm
  · simpa [h.map_zero, h.energy_zero] using
      P.sequentialRelaxation_toAmbient_le (0 : P.Test)
  · exact bot_le

end Quadratic

end FunctionalInequalities.Energy.PreEnergy
