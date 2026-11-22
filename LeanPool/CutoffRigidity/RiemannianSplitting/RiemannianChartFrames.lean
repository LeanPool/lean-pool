/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Actual coordinate-constant tangent frames
The inverse tangent-bundle chart trivialization supplies local coordinate vectors.
-/

@[expose] public section
open Bundle Set Filter VectorField
open scoped Manifold ContDiff Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- The actual inverse tangent trivialization, used as a coordinate-constant
frame without assuming any parallelism of that frame. -/
noncomputable def chartFrameCLM (x₀ y : M) : E →L[ℝ] TangentSpace I y :=
  (trivializationAt E (TangentSpace I) x₀).symmL ℝ y

/-- The vector in the coordinate frame corresponding to a fixed model-space vector. -/
noncomputable def chartFrame (x₀ : M) (u : E) (y : M) : TangentSpace I y :=
  chartFrameCLM (I := I) x₀ y u

theorem chartFrame_self (x₀ : M) (u : E) : chartFrame (I := I) x₀ u x₀ = u := by
  rw [chartFrame, chartFrameCLM, TangentBundle.symmL_trivializationAt (by simp),
    mfderivWithin_range_extChartAt_symm]
  rfl

/-- The actual coordinate-constant tangent frame is C¹ near its chart center. -/
theorem contMDiffAt_chartFrame (x₀ : M) (u : E) :
    ContMDiffAt I I.tangent 1 (T% (chartFrame (I := I) x₀ u)) x₀ := by
  rw [contMDiffAt_section_iff]
  apply (contMDiffAt_const (c := u)).congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds H x₀] with y hy
  have hy' : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hy
  change (trivializationAt E (TangentSpace I) x₀ ⟨y, chartFrame (I := I) x₀ u y⟩).2 = _
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy']
  exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL hy' u

end CutoffRigidity
