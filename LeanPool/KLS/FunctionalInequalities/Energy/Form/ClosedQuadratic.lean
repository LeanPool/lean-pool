/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Form.Functional
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Closed extended quadratic energies

This module records closed-quadratic-form structure as properties of an existing
`Energy.Functional`. The carrier remains the ambient real normed space, and the functional may
take the value `⊤` away from its finite domain.

Homogeneity is stored only for nonzero scalars. The separate zero field supplies the missing
branch without interpreting the indeterminate expression `0 * ⊤`. The derived theorem
`ClosedQuadratic.smul` exposes both branches in one total statement.
-/

@[expose] public section

namespace FunctionalInequalities.Energy

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- An extended energy is a densely defined closed quadratic form.

The parallelogram identity is stated in `ENNReal`, so it also constrains points outside the finite
domain. Lower semicontinuity is the closedness condition, while `dense_domain` records that finite
energy tests are dense in the ambient norm topology.
-/
structure ClosedQuadratic (energy : Functional X) : Prop where
  /-- The zero vector has zero energy. -/
  zero : energy 0 = 0
  /-- Nonzero real scaling multiplies energy by the square of the scalar.

  The hypothesis `c ≠ 0` deliberately excludes `0 * ⊤`; the zero branch is the preceding
  field.
  -/
  smul_of_ne_zero : ∀ (c : ℝ), c ≠ 0 → ∀ x : X,
    energy (c • x) = ENNReal.ofReal (c ^ 2) * energy x
  /-- The extended parallelogram identity. -/
  parallelogram : ∀ x y : X,
    energy (x + y) + energy (x - y) = 2 * energy x + 2 * energy y
  /-- Closedness of the extended energy. -/
  lowerSemicontinuous : LowerSemicontinuous fun x ↦ energy x
  /-- The finite-energy domain is dense in the ambient norm topology. -/
  dense_domain : Dense energy.domain

namespace ClosedQuadratic

variable {energy : Functional X}

/-- A closed quadratic energy is zero preserving. -/
theorem zeroEnergy (h : ClosedQuadratic energy) : ZeroEnergy energy :=
  h.zero

/-- The zero vector lies in the finite-energy domain. -/
theorem zero_mem_domain (h : ClosedQuadratic energy) : (0 : X) ∈ energy.domain :=
  h.zeroEnergy.zero_mem_domain

/-- The finite domain of a closed quadratic energy, as a real submodule of the ambient space. -/
def domainSubmodule (h : ClosedQuadratic energy) : Submodule ℝ X where
  carrier := energy.domain
  zero_mem' := h.zero_mem_domain
  add_mem' := by
    intro x y hx hy
    change energy (x + y) ≠ ⊤
    have hright : 2 * energy x + 2 * energy y ≠ ⊤ := by
      rw [ENNReal.add_ne_top]
      exact ⟨ENNReal.mul_ne_top (by simp) hx, ENNReal.mul_ne_top (by simp) hy⟩
    have hleft : energy (x + y) + energy (x - y) ≠ ⊤ := by
      rw [h.parallelogram x y]
      exact hright
    exact (ENNReal.add_ne_top.mp hleft).1
  smul_mem' := by
    intro c x hx
    by_cases hc : c = 0
    · subst c
      simpa using h.zero_mem_domain
    · change energy (c • x) ≠ ⊤
      rw [h.smul_of_ne_zero c hc x]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx

/-- Membership in the domain submodule is exactly finiteness of the extended energy. -/
@[simp]
theorem mem_domainSubmodule (h : ClosedQuadratic energy) (x : X) :
    x ∈ h.domainSubmodule ↔ energy.FiniteAt x :=
  Iff.rfl

/-- Scalar homogeneity as a total statement with an explicit zero branch.

In particular, scaling an infinite-energy vector by zero yields zero energy without relying on
the multiplication convention for `0 * ⊤` in `ENNReal`.
-/
theorem smul (h : ClosedQuadratic energy) (c : ℝ) (x : X) :
    energy (c • x) =
      if c = 0 then 0 else ENNReal.ofReal (c ^ 2) * energy x := by
  by_cases hc : c = 0
  · subst c
    simp [h.zero]
  · simpa [hc] using h.smul_of_ne_zero c hc x

section Transport

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Pulling a closed quadratic energy back along a linear isometric equivalence preserves all
closed-quadratic structure.

Surjectivity is essential for the density conclusion. A mere linear isometric embedding need
not have dense preimage of the finite-energy domain.
-/
theorem comap_linearIsometryEquiv (h : ClosedQuadratic energy)
    (e : Y ≃ₗᵢ[ℝ] X) : ClosedQuadratic (energy.comap e) where
  zero := by simpa using h.zero
  smul_of_ne_zero c hc y := by
    simpa using h.smul_of_ne_zero c hc (e y)
  parallelogram x y := by
    simpa using h.parallelogram (e x) (e y)
  lowerSemicontinuous := by
    simpa only [Functional.comap_apply, Function.comp_def] using
      h.lowerSemicontinuous.comp e.continuous
  dense_domain := by
    change Dense (e ⁻¹' energy.domain)
    exact h.dense_domain.preimage e.toHomeomorph.isOpenMap

end Transport

end ClosedQuadratic

end FunctionalInequalities.Energy
