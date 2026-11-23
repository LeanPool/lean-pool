/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedInterface

/-! # Smoothness at a point of a tangent vector field -/

@[expose] public section
open Bundle Filter Set VectorField
open scoped Manifold ContDiff Topology

namespace CutCur.WBoch

section Defs

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- `Y` is a smooth section of the tangent bundle at `x`. -/
def SmAt (X : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x : M) : Prop :=
  ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% X) x

end Defs

end CutCur.WBoch
