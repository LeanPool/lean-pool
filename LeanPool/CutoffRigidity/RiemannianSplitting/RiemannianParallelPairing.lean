/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelFields
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic

/-! # Constant inner products of parallel fields -/

@[expose] public section
open Bundle
open scoped Manifold ContDiff

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [PreconnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The Gram function of two actual parallel fields is globally constant on a
connected manifold. -/
theorem inner_parallel_eq_of_preconnected
    {X Y : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent 1 (T% X)) (hY : ContMDiff I I.tangent 1 (T% Y))
    (hpX : ∀ x, CovariantDerivative.leviCivitaConnection I M X x = 0)
    (hpY : ∀ x, CovariantDerivative.leviCivitaConnection I M Y x = 0)
    (x y : M) : inner ℝ (X x) (Y x) = inner ℝ (X y) (Y y) := by
  have metric := CovariantDerivative.isMetricCompatible_leviCivitaConnection (M := M) I
  exact metric.inner_eq_of_isPreconnected_of_cov_eq_zero isOpen_univ isPreconnected_univ
    (hX.mdifferentiable one_ne_zero).mdifferentiableOn
    (hY.mdifferentiable one_ne_zero).mdifferentiableOn
    (fun z _ => hpX z) (fun z _ => hpY z) (Set.mem_univ x) (Set.mem_univ y)

end CutoffRigidity
