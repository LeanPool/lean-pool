/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianCoordinateGradient
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChristoffel
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartVolumeDensity
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianDifferentialOperators

/-! # Chart-frame calculus at every point of a chart (not only at its center)

The existing `Riemannian*` files compute with the frame `chartFrame x₀` at the chart center `x₀`.
For the integration by parts on a weighted manifold we need the same facts at every point of the
source of the chart `chartAt F x₀`, for the model `𝓘(ℝ, F)`.
-/

@[expose] public section
open Bundle Set Filter VectorField
open scoped Manifold ContDiff Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace CutoffRigidity

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) 2 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) 2 M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem extChartAt_symm_mem_source {x₀ : M} {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    (extChartAt 𝓘(ℝ, F) x₀).symm z ∈ (chartAt F x₀).source := by
  simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, F) x₀).map_target hz

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) 2 M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem extChartAt_target_nhds {x₀ : M} {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    (extChartAt 𝓘(ℝ, F) x₀).target ∈ 𝓝 z :=
  extChartAt_target_mem_nhds' hz

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- The actual chart frame is C¹ at every point of the chart source. -/
theorem contMDiffAt_chartFrame_source {x₀ y : M} (hy : y ∈ (chartAt F x₀).source) (u : F) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent 1 (T% (chartFrame (I := 𝓘(ℝ, F)) x₀ u)) y := by
  have hy' : y ∈ (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).baseSet := by simpa using hy
  rw [Trivialization.contMDiffAt_section_iff (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀) hy']
  apply (contMDiffAt_const (c := u)).congr_of_eventuallyEq
  filter_upwards [(chartAt F x₀).open_source.mem_nhds hy] with y' hy''
  have hy3 : y' ∈ (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).baseSet := by simpa using hy''
  change (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀ ⟨y', chartFrame (I := 𝓘(ℝ, F)) x₀ u y'⟩).2
      = _
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy3]
  exact (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt_symmL hy3 u

omit [FiniteDimensional ℝ F] in
theorem contMDiffAt_chartFrame_inner_source {x₀ y : M} (hy : y ∈ (chartAt F x₀).source) (u v : F) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 1
      (fun y' ↦ inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ u y')
        (chartFrame (I := 𝓘(ℝ, F)) x₀ v y')) y :=
  ContMDiffAt.inner_bundle (E := TangentSpace 𝓘(ℝ, F))
    (contMDiffAt_chartFrame_source hy u) (contMDiffAt_chartFrame_source hy v)

/-- The chart metric is C¹ at every point of the chart target. -/
theorem contDiffAt_chartMetric_target (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    ContDiffAt ℝ 1 (chartMetric (I := 𝓘(ℝ, F)) x₀) z := by
  have hsymm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) 1 (extChartAt 𝓘(ℝ, F) x₀).symm z :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt (extChartAt_target_nhds hz)
  rw [← contDiffWithinAt_univ]
  apply contDiffWithinAt_clm_apply.mpr
  intro u
  apply contDiffWithinAt_clm_apply.mpr
  intro v
  have hinner := (contMDiffAt_chartFrame_inner_source (extChartAt_symm_mem_source hz) u v).comp z
    hsymm
  have hreal := hinner.contDiffAt.contDiffWithinAt (s := univ)
  simpa only [Function.comp_def, chartMetric_apply] using hreal

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) 2 M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem chartCoordinateField_eq_mpullback (x₀ : M) (X : (x : M) → TangentSpace 𝓘(ℝ, F) x) (z : F) :
    chartCoordinateField (I := 𝓘(ℝ, F)) x₀ X z =
      mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) (extChartAt 𝓘(ℝ, F) x₀).symm X z := by
  simp only [chartCoordinateField, mpullbackWithin, mpullback,
    ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ]
  rfl

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem chartFrame_eq_mfderiv (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (v : F) :
    chartFrame (I := 𝓘(ℝ, F)) x₀ v ((extChartAt 𝓘(ℝ, F) x₀).symm z) =
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (extChartAt 𝓘(ℝ, F) x₀).symm z v := by
  have hy := extChartAt_symm_mem_source hz
  unfold chartFrame chartFrameCLM
  rw [TangentBundle.symmL_trivializationAt hy, (extChartAt 𝓘(ℝ, F) x₀).right_inv hz]
  simp [mfderivWithin_univ]
  rfl

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- The Lie bracket of a chart-constant frame field with an arbitrary differentiable field,
at an arbitrary point of the chart. -/
theorem mlieBracket_chartFrame_left_source (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (u : F)
    {Y : (x : M) → TangentSpace 𝓘(ℝ, F) x}
    (hY : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% Y) ((extChartAt 𝓘(ℝ, F) x₀).symm z)) :
    mlieBracket 𝓘(ℝ, F) (chartFrame (I := 𝓘(ℝ, F)) x₀ u) Y
        ((extChartAt 𝓘(ℝ, F) x₀).symm z) =
      chartFrame (I := 𝓘(ℝ, F)) x₀
        (fderiv ℝ (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y) z u)
        ((extChartAt 𝓘(ℝ, F) x₀).symm z) := by
  have hsymm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) 2 (extChartAt 𝓘(ℝ, F) x₀).symm z :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt (extChartAt_target_nhds hz)
  have hfr := (contMDiffAt_chartFrame_source (extChartAt_symm_mem_source hz) u).mdifferentiableAt
    one_ne_zero
  have : IsManifold 𝓘(ℝ, F) (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have key := mpullback_mlieBracket (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, F)) (n := 2) hfr hY hsymm
    (by simp)
  have hconst : mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) (extChartAt 𝓘(ℝ, F) x₀).symm
      (chartFrame (I := 𝓘(ℝ, F)) x₀ u) =ᶠ[𝓝 z] fun _ => u := by
    filter_upwards [extChartAt_target_nhds hz] with z' hz'
    rw [← chartCoordinateField_eq_mpullback]
    exact chartCoordinateField_frame (I := 𝓘(ℝ, F)) x₀ u hz'
  have hR : mlieBracket 𝓘(ℝ, F) (mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) (extChartAt 𝓘(ℝ, F) x₀).symm
      (chartFrame (I := 𝓘(ℝ, F)) x₀ u)) (mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) (extChartAt 𝓘(ℝ, F) x₀).symm Y) z
      = fderiv ℝ (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y) z u := by
    rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
    erw [lieBracketWithin_univ]
    erw [lieBracket_eq]
    dsimp only
    rw [hconst.fderiv_eq, hconst.self_of_nhds]
    have hcf : chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y =
        mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) (extChartAt 𝓘(ℝ, F) x₀).symm Y :=
      funext (chartCoordinateField_eq_mpullback x₀ Y)
    rw [hcf]
    have zeroDerivative : fderiv ℝ (fun _ : F ↦ u) z = (0 : F →L[ℝ] F) := fderiv_const_apply _
    erw [zeroDerivative]
    exact sub_zero _
  rw [hR] at key
  have hinv := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, F)) hz
  simp only [ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ] at hinv
  have h2 := hinv.inverse_apply_eq.mp key
  rw [chartFrame_eq_mfderiv x₀ hz]
  exact h2

/-- Derivative of the chart metric in the coordinate direction of `X`, at any point of the chart. -/
theorem fderiv_chartMetric_direction_source (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (X : (x : M) → TangentSpace 𝓘(ℝ, F) x)
    (u v : F) :
    ((fderiv ℝ (chartMetric (I := 𝓘(ℝ, F)) x₀) z)
      (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ X z)) u v =
    mvfderiv 𝓘(ℝ, F) (fun y ↦ inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ u y)
      (chartFrame (I := 𝓘(ℝ, F)) x₀ v y)) ((extChartAt 𝓘(ℝ, F) x₀).symm z)
      (X ((extChartAt 𝓘(ℝ, F) x₀).symm z)) := by
  let e := extChartAt 𝓘(ℝ, F) x₀
  let f : M → ℝ := fun y ↦ inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ u y)
    (chartFrame (I := 𝓘(ℝ, F)) x₀ v y)
  have hf : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f (e.symm z) :=
    (contMDiffAt_chartFrame_inner_source (extChartAt_symm_mem_source hz) u v).mdifferentiableAt
      one_ne_zero
  have hMetricFD := ((contDiffAt_chartMetric_target (F := F) x₀ hz).differentiableAt
    one_ne_zero).hasFDerivAt
  have hpair := (hMetricFD.clm_apply (hasFDerivAt_const u z)).clm_apply (hasFDerivAt_const v z)
  change HasFDerivAt (f ∘ e.symm) _ z at hpair
  let coord := chartCoordinateField (I := 𝓘(ℝ, F)) x₀ X z
  have hpairAtCoord := congrArg (fun L : F →L[ℝ] ℝ ↦ L coord) hpair.fderiv.symm
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add] at hpairAtCoord
  have derivative := fderiv_chartScalar_frame x₀ hz hf coord
  rw [chartFrame_chartCoordinateField x₀ hz X] at derivative
  exact hpairAtCoord.trans derivative

/-- Koszul formula for `⟨∇_{e_u} Y, e_u⟩` in the chart frame, at any point of the chart:
`⟨∇_{e_u} Y, e_u⟩ = ½ (∂_Y g)(u,u) + g(u, ∂_u Y)`. -/
theorem inner_leviCivita_chartFrame_self (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (u : F)
    {Y : (x : M) → TangentSpace 𝓘(ℝ, F) x}
    (hY : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% Y) ((extChartAt 𝓘(ℝ, F) x₀).symm z)) :
    inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y
        ((extChartAt 𝓘(ℝ, F) x₀).symm z)
        (chartFrame (I := 𝓘(ℝ, F)) x₀ u ((extChartAt 𝓘(ℝ, F) x₀).symm z)))
      (chartFrame (I := 𝓘(ℝ, F)) x₀ u ((extChartAt 𝓘(ℝ, F) x₀).symm z)) =
    (fderiv ℝ (chartMetric (I := 𝓘(ℝ, F)) x₀) z
        (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y z)) u u / 2 +
      chartMetric (I := 𝓘(ℝ, F)) x₀ z u (fderiv ℝ (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ Y) z u)
          := by
  have hX := (contMDiffAt_chartFrame_source (extChartAt_symm_mem_source hz) u).mdifferentiableAt
    one_ne_zero
  have hh := CovariantDerivative.leviCivitaConnection_apply_inner (I := 𝓘(ℝ, F)) hX hY hX
  have hc : (fun x => inner ℝ (Y x) (chartFrame (I := 𝓘(ℝ, F)) x₀ u x)) =
      fun x => inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ u x) (Y x) :=
    funext fun x => real_inner_comm _ _
  rw [hc, mlieBracket_self] at hh
  dsimp only at hh
  rw [mlieBracket_swap_apply, mlieBracket_chartFrame_left_source x₀ hz u hY] at hh
  rw [fderiv_chartMetric_direction_source x₀ hz Y u u]
  simp only [Pi.zero_apply, inner_zero_right, inner_neg_right, chartMetric_apply] at hh ⊢
  linarith

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) 2 M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem extChartAt_target_eq (x₀ : M) :
    (extChartAt 𝓘(ℝ, F) x₀).target = (chartAt F x₀).target := by
  simp [extChartAt, OpenPartialHomeomorph.extend]

end CutoffRigidity
