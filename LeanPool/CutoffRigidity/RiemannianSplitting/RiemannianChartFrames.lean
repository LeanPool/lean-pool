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
The frame is the inverse of the actual tangent-bundle chart trivialization.
Its pullback by the actual chart inverse is constant, which computes its Lie
bracket with an arbitrary actual vector field without a coordinate premise.
-/

@[expose] public section
open Bundle Set Filter VectorField
open scoped Manifold ContDiff Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]

/-- The actual inverse tangent trivialization, used as a coordinate-constant
frame without assuming any parallelism of that frame. -/
noncomputable def chartFrameCLM (x₀ y : M) : E →L[ℝ] TangentSpace I y :=
  (trivializationAt E (TangentSpace I) x₀).symmL ℝ y

/-- The vector in the coordinate frame corresponding to a fixed model-space vector. -/
noncomputable def chartFrame (x₀ : M) (u : E) (y : M) : TangentSpace I y :=
  chartFrameCLM (I := I) x₀ y u

/-- The actual chart expression of a tangent field. -/
noncomputable def chartCoordinateField (x₀ : M) (X : (x : M) → TangentSpace I x) (z : E) : E :=
  mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm X (range I) z

omit [BoundarylessManifold I M] in
theorem chartFrame_self (x₀ : M) (u : E) : chartFrame (I := I) x₀ u x₀ = u := by
  rw [chartFrame, chartFrameCLM, TangentBundle.symmL_trivializationAt (by simp),
    mfderivWithin_range_extChartAt_symm]
  rfl

omit [BoundarylessManifold I M] in
/-- Actual chart pullback sends the actual chart-constant frame to the specified
constant model vector on the whole chart target. -/
theorem chartCoordinateField_frame (x₀ : M) (u : E) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    chartCoordinateField (I := I) x₀ (chartFrame (I := I) x₀ u) z = u := by
  let e := extChartAt I x₀
  let y := e.symm z
  have hy : y ∈ e.source := e.map_target hz
  have hychart : y ∈ (chartAt H x₀).source := by simpa only [e, extChartAt_source] using hy
  have hinv : (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) z).inverse = mfderiv I 𝓘(ℝ, E) e y :=
    ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hz)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hz)
  change (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) z).inverse (chartFrame (I := I) x₀ u y) = u
  rw [hinv, ← TangentBundle.continuousLinearMapAt_trivializationAt hychart]
  exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL
    (by simpa using hychart) u

omit [BoundarylessManifold I M] in
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

/-- Actual pullback of the coordinate frame is constant on a neighborhood of
the coordinate center, since that center lies in the interior of the target. -/
theorem chartCoordinateField_frame_eventuallyEq (x₀ : M) (u : E) :
    chartCoordinateField (I := I) x₀ (chartFrame (I := I) x₀ u) =ᶠ[𝓝 (extChartAt I x₀ x₀)] (fun _
      ↦ u) := by
  have htarget : (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ x₀) :=
    mem_of_superset (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))) interior_subset
  filter_upwards [htarget] with z hz
  exact chartCoordinateField_frame (I := I) x₀ u hz

omit [BoundarylessManifold I M] in
/-- At the chart center, actual chart pullback records the vector itself in
the model coordinates. -/
theorem chartCoordinateField_self (x₀ : M) (X : (x : M) → TangentSpace I x) :
    chartCoordinateField (I := I) x₀ X (extChartAt I x₀ x₀) = X x₀ := by
  change (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I)
    (extChartAt I x₀ x₀)).inverse (X ((extChartAt I x₀).symm (extChartAt I x₀ x₀))) = _
  convert! mfderivWithin_extChartAt_symm_inverse_apply (I := I) (X x₀) using 1
  rw [extChartAt_to_inv]

/-- The actual Lie bracket with a coordinate-constant frame computes the
negative actual coordinate derivative of the vector field at the chart center. -/
theorem mlieBracket_chartFrame (x₀ : M) (u : E)
    (X : (x : M) → TangentSpace I x) :
    mlieBracket I X (chartFrame (I := I) x₀ u) x₀ =
      chartFrame (I := I) x₀
        (-(fderiv ℝ (chartCoordinateField (I := I) x₀ X) (extChartAt I x₀ x₀)) u) x₀ := by
  have hRange : range I ∈ 𝓝 (extChartAt I x₀ x₀) :=
    range_mem_nhds_isInteriorPoint (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀))
  have hconst := chartCoordinateField_frame_eventuallyEq (I := I) x₀ u
  have hD : fderivWithin ℝ (chartCoordinateField (I := I) x₀ (chartFrame (I := I) x₀ u))
      (range I) (extChartAt I x₀ x₀) = 0 := by
    rw [fderivWithin_of_mem_nhds hRange, hconst.fderiv_eq]
    simp
  rw [chartFrame_self]
  rw [← mlieBracketWithin_univ, mlieBracketWithin_apply, mfderiv_extChartAt_self]
  have inverseId : (ContinuousLinearMap.id ℝ (TangentSpace I x₀)).inverse =
      ContinuousLinearMap.id ℝ (TangentSpace I x₀) := ContinuousLinearMap.inverse_id
  erw [inverseId]
  simp only [preimage_univ, univ_inter]
  change lieBracketWithin ℝ (chartCoordinateField (I := I) x₀ X)
    (chartCoordinateField (I := I) x₀ (chartFrame (I := I) x₀ u))
    (range I) (extChartAt I x₀ x₀) = _
  rw [lieBracketWithin_eq]
  dsimp only
  rw [hD, zero_apply, zero_sub,
    chartCoordinateField_frame (I := I) x₀ u (mem_extChartAt_target x₀),
    fderivWithin_of_mem_nhds hRange]

end CutoffRigidity
