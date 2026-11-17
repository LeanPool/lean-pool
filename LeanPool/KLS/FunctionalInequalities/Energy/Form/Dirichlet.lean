/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Form.ClosedQuadratic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Markovian and Dirichlet energies on real `L²`

The extended functional, closed-quadratic structure, and Markov property are separate layers.
This module formulates the Markov property through all normal contractions of the real line.
Mathlib's `LipschitzWith.compLp` makes those contractions well defined on `L²` equivalence
classes, so no pointwise representative is chosen by the public API.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Energy

/-- A normal contraction of the real line: it fixes zero and has Lipschitz constant at most one. -/
structure NormalContraction where
  /-- The underlying real function. -/
  toFun : ℝ → ℝ
  /-- The contraction estimate. -/
  lipschitz : LipschitzWith 1 toFun
  /-- Normalization at zero. -/
  map_zero : toFun 0 = 0

namespace NormalContraction

instance : CoeFun NormalContraction fun _ ↦ ℝ → ℝ :=
  ⟨NormalContraction.toFun⟩

/-- A normal contraction acts on a real `L²` space by composition. -/
def compL2 {α : Type*} [MeasurableSpace α] (φ : NormalContraction) (μ : Measure α)
    (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  φ.lipschitz.compLp φ.map_zero f

/-- The `L²` action agrees almost everywhere with pointwise composition. -/
theorem coeFn_compL2 {α : Type*} [MeasurableSpace α] (φ : NormalContraction)
    (μ : Measure α) (f : Lp ℝ 2 μ) :
    φ.compL2 μ f =ᵐ[μ] fun x ↦ φ (f x) := by
  simpa [compL2, Function.comp_def] using φ.lipschitz.coeFn_compLp φ.map_zero f

/-- Every normal contraction sends the zero element of `L²` to zero. -/
@[simp]
theorem compL2_zero {α : Type*} [MeasurableSpace α] (φ : NormalContraction)
    (μ : Measure α) : φ.compL2 μ (0 : Lp ℝ 2 μ) = 0 :=
  φ.lipschitz.compLp_zero φ.map_zero

end NormalContraction

/-- An extended `L²` energy is Markovian when normal contractions do not increase it. -/
def Markovian {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (energy : Functional (Lp ℝ 2 μ)) : Prop :=
  ∀ (φ : NormalContraction) (f : Lp ℝ 2 μ), energy (φ.compL2 μ f) ≤ energy f

/-- A Dirichlet energy is a closed quadratic energy with the normal-contraction property.

This is a property bundle over an existing extended functional. It does not select a canonical
energy for a measure and does not identify any concrete smooth core with the finite domain.
-/
structure Dirichlet {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (energy : Functional (Lp ℝ 2 μ)) : Prop where
  /-- Closed quadratic-form structure on the ambient real `L²` space. -/
  closedQuadratic : ClosedQuadratic energy
  /-- Stability under all normal contractions. -/
  markovian : Markovian μ energy

namespace Dirichlet

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {energy : Functional (Lp ℝ 2 μ)}

/-- A Dirichlet energy vanishes at the zero element. -/
theorem zeroEnergy (h : Dirichlet μ energy) : ZeroEnergy energy :=
  h.closedQuadratic.zeroEnergy

/-- The zero element belongs to the finite domain of a Dirichlet energy. -/
theorem zero_mem_domain (h : Dirichlet μ energy) : (0 : Lp ℝ 2 μ) ∈ energy.domain :=
  h.closedQuadratic.zero_mem_domain

end Dirichlet

end FunctionalInequalities.Energy
