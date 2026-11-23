/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # Volume density in an inverse chart -/

@[expose] public section

open Bundle
open scoped Manifold

namespace CutCur

/-- The square root of the Gram determinant of a linear map on an orthonormal basis. -/
noncomputable def gramDens {F W : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (L : F →ₗ[ℝ] W) : ℝ :=
  Real.sqrt (Matrix.gram ℝ (fun i ↦ L (stdOrthonormalBasis ℝ F i))).det

/-- The Riemannian density of the inverse of a chart `Ξ` at `z`. -/
noncomputable def chartDensity {F M : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace F M]
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
    (Ξ : OpenPartialHomeomorph M F) (z : F) : ℝ :=
  gramDens (show F →ₗ[ℝ] TangentSpace 𝓘(ℝ, F) (Ξ.symm z) from
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) Ξ.symm z).toLinearMap)

end CutCur
