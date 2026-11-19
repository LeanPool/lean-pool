/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.LocalSetDefinitions
public import LeanPool.StableManifold.Linear.Subspaces
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic

/-! # Spectral hyperbolicity of a real linear map -/

@[expose] public section

namespace ContinuousLinearMap

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear map is **hyperbolic** if it has no eigenvalue of absolute value `1`: no complex root
of its characteristic polynomial has modulus `1`. (A real operator may have non-real eigenvalues,
so the eigenvalues are the complex roots of `LinearMap.charpoly`.) -/
def IsHyperbolic (A : E →L[ℝ] E) : Prop :=
  ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (A : E →ₗ[ℝ] E)) = 0 → ‖μ‖ ≠ 1

end FiniteDimensional

end ContinuousLinearMap
