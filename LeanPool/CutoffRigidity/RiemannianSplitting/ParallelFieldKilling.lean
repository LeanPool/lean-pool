/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelFields

/-! # Parallel fields satisfy the actual Killing identity
This is the infinitesimal metric-preservation calculation in the splitting
proof. It uses the actual Levi-Civita derivative and actual manifold Lie bracket.
The passage from this identity to isometry of the global flow requires genuine
spatial differentiability of that flow and is not asserted here.
-/

@[expose] public section
open Bundle
open scoped Manifold ContDiff

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- For an actual parallel field `X`, the Lie derivative of the actual metric
vanishes on differentiable tangent fields `Y,Z`. -/
theorem parallel_field_killing_identity
    {X Y Z : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent (T% X) x)
    (hY : MDifferentiableAt I I.tangent (T% Y) x)
    (hZ : MDifferentiableAt I I.tangent (T% Z) x)
    (hpX : CovariantDerivative.leviCivitaConnection I M X x = 0) :
    mvfderiv I (fun y ↦ inner ℝ (Y y) (Z y)) x (X x) =
      inner ℝ (VectorField.mlieBracket I X Y x) (Z x) +
      inner ℝ (Y x) (VectorField.mlieBracket I X Z x) := by
  let cov := CovariantDerivative.leviCivitaConnection I M
  have hmetric := (CovariantDerivative.isMetricCompatible_leviCivitaConnection I
    (M := M)).mvfderiv_inner_eq X hY hZ
  have hYbr := (CovariantDerivative.torsion_eq_zero_iff cov).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) hX hY
  have hZbr := (CovariantDerivative.torsion_eq_zero_iff cov).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) hX hZ
  have hYcov : cov Y x (X x) = VectorField.mlieBracket I X Y x := by
    simpa [cov, hpX] using hYbr
  have hZcov : cov Z x (X x) = VectorField.mlieBracket I X Z x := by
    simpa [cov, hpX] using hZbr
  simpa only [← hYcov, ← hZcov] using hmetric

/-- In particular, a field commuting with an actual parallel field has
constant squared norm in that parallel direction. -/
theorem mvfderiv_inner_self_eq_zero_of_parallel_commute
    {X Y : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent (T% X) x)
    (hY : MDifferentiableAt I I.tangent (T% Y) x)
    (hpX : CovariantDerivative.leviCivitaConnection I M X x = 0)
    (hbr : VectorField.mlieBracket I X Y x = 0) :
    mvfderiv I (fun y ↦ inner ℝ (Y y) (Y y)) x (X x) = 0 := by
  simpa only [hbr, inner_zero_left, inner_zero_right, zero_add] using
    parallel_field_killing_identity hX hY hY hpX

end CutoffRigidity
