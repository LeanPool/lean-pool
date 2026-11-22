/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelFields
public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldZeroDifferential

/-! # Constant inner products of parallel fields -/

@[expose] public section
open Bundle
open scoped Manifold ContDiff

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [BoundarylessManifold I M] [PreconnectedSpace M]
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
  have hdX := hX.mdifferentiable one_ne_zero
  have hdY := hY.mdifferentiable one_ne_zero
  have hf : MDifferentiable I 𝓘(ℝ, ℝ) (fun z ↦ inner ℝ (X z) (Y z)) :=
    fun z ↦ MDifferentiableAt.inner_bundle (E := TangentSpace I) (hdX z) (hdY z)
  apply eq_of_mvfderiv_eq_zero hf _ x y
  intro z
  ext v
  exact mvfderiv_inner_parallel_eq_zero (CovariantDerivative.leviCivitaConnection I M)
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) hdX hdY hpX hpY z v

end CutoffRigidity
