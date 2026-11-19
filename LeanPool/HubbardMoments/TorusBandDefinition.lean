/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Single-particle energies on the square torus -/

@[expose] public section

namespace HubbardMoments

/-- **The tight-binding band of the `L × L` torus**: the single-particle energies
`ε(q) = -2t (cos q₁ + cos q₂)` at the `L²` momenta `q = 2π (m₁, m₂)/L`. -/
noncomputable def torusBand (L : ℕ) (t : ℝ) : Fin L × Fin L → ℝ := fun m =>
  -2 * t * (Real.cos (2 * Real.pi * (m.1 : ℕ) / L) + Real.cos (2 * Real.pi * (m.2 : ℕ) / L))

end HubbardMoments
