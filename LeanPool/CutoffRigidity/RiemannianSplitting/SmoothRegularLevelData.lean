/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.SmoothRegularLevelCoordinates
public import LeanPool.CutoffRigidity.RiemannianSplitting.RegularLevelChartedSpace

/-! # Constructive smooth regular-level chart data
The actual implicit coordinates and their smoothness witnesses are retained,
so subsequent atlas compatibility does not rely on a topological-chart choice.
-/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Actual coordinates for a regular zero level, including the actual smooth
ambient extension and its actual smooth inverse. -/
structure SmoothRegularLevelData (f : M → ℝ) (x : {y : M // f y = 0}) where
  /-- Local coordinates with the given defining function in the first component. -/
  coordinates : OpenPartialHomeomorph E (ℝ ×
    (fderiv ℝ (f ∘ (extChartAt I x.val).symm) (extChartAt I x.val x.val)).ker)
  center_mem : extChartAt I x.val x.val ∈ coordinates.source
  source_subset : coordinates.source ⊆ (extChartAt I x.val).target
  center_eq : coordinates (extChartAt I x.val x.val) = (0, 0)
  first_eq : ∀ z, (coordinates z).1 = f ((extChartAt I x.val).symm z)
  smooth : ContDiffOn ℝ 2 coordinates coordinates.source
  smooth_symm : ContDiffOn ℝ 2 coordinates.symm coordinates.target
  /-- A linear equivalence from the kernel to the fixed level model space. -/
  modelEquiv : (fderiv ℝ (f ∘ (extChartAt I x.val).symm)
      (extChartAt I x.val x.val)).ker ≃L[ℝ]
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))

omit [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- Actual `C²` regular scalar functions supply all data above by the actual
implicit theorem and actual rank-nullity. -/
theorem nonempty_smoothRegularLevelData {f : M → ℝ} (x : {y : M // f y = 0})
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x.val)
    (X : (y : M) → TangentSpace I y) (hne : mvfderiv I f x.val (X x.val) ≠ 0) :
    Nonempty (SmoothRegularLevelData (I := I) f x) := by
  obtain ⟨e, he, heSubset, heCenter, heFirst, hforward, hbackward⟩ :=
    exists_finiteSmooth_regularScalar_coordinates x.val hf (by norm_num) X hne
  let D := fderiv ℝ (f ∘ (extChartAt I x.val).symm) (extChartAt I x.val x.val)
  have hdim : Module.finrank ℝ D.ker =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) := by
    rw [finrank_ker_scalar_of_surjective D
      (surjective_fderiv_chartScalar x.val (hf.mdifferentiableAt (by norm_num)) X hne)]
    simp
  exact ⟨{ coordinates := e
           center_mem := he
           source_subset := heSubset
           center_eq := by simpa only [x.property] using heCenter
           first_eq := heFirst
           smooth := hforward
           smooth_symm := hbackward
           modelEquiv := ContinuousLinearEquiv.ofFinrankEq hdim }⟩

namespace SmoothRegularLevelData
variable {f : M → ℝ} {x : {y : M // f y = 0}}

/-- The actual full ambient scalar coordinate chart. -/
noncomputable def ambientChart (d : SmoothRegularLevelData (I := I) f x) :=
  (boundarylessExtChart (I := I) x.val).trans d.coordinates

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- Its scalar coordinate is the original potential wherever the actual chart
is defined. -/
theorem ambientChart_first (d : SmoothRegularLevelData (I := I) f x)
    (y : M) (hy : y ∈ d.ambientChart.source) : (d.ambientChart y).1 = f y := by
  change (d.coordinates (extChartAt I x.val y)).1 = f y
  rw [d.first_eq, (extChartAt I x.val).left_inv hy.1]

/-- The actual regular-level chart with the common Euclidean model. -/
noncomputable def levelChart (d : SmoothRegularLevelData (I := I) f x) :
    OpenPartialHomeomorph {y : M // f y = 0}
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) :=
  (scalarLevelChart f d.ambientChart d.ambientChart_first x).trans
    d.modelEquiv.toHomeomorph.toOpenPartialHomeomorph

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
theorem center_mem_levelChart_source (d : SmoothRegularLevelData (I := I) f x) :
    x ∈ d.levelChart.source := by
  refine ⟨?_, mem_univ _⟩
  exact ⟨mem_extChartAt_source x.val, d.center_mem⟩

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
@[simp] theorem levelChart_center (d : SmoothRegularLevelData (I := I) f x) :
    d.levelChart x = 0 := by
  change d.modelEquiv (d.coordinates (extChartAt I x.val x.val)).2 = 0
  rw [d.center_eq, map_zero]

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The level-chart forward coordinates are the explicit smooth ambient
coordinates followed by the fixed linear kernel identification. -/
theorem levelChart_apply (d : SmoothRegularLevelData (I := I) f x)
    (y : {y : M // f y = 0}) :
    d.levelChart y = d.modelEquiv (d.coordinates (extChartAt I x.val y.val)).2 := by
  simp only [levelChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    scalarLevelChart_apply, ambientChart, boundarylessExtChart_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph]

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- Exact source membership for the constructed level chart. -/
theorem mem_levelChart_source (d : SmoothRegularLevelData (I := I) f x)
    (y : {y : M // f y = 0}) :
    y ∈ d.levelChart.source ↔ y.val ∈ (extChartAt I x.val).source ∧
      extChartAt I x.val y.val ∈ d.coordinates.source := by
  simp only [levelChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ,
    scalarLevelChart_source, Set.mem_preimage, ambientChart,
    boundarylessExtChart, Set.mem_inter_iff]
  rfl

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- Exact target membership for the constructed level chart. -/
theorem mem_levelChart_target (d : SmoothRegularLevelData (I := I) f x)
    (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) :
    z ∈ d.levelChart.target ↔
      (0, d.modelEquiv.symm z) ∈ d.ambientChart.target := by
  simp only [levelChart, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter,
    scalarLevelChart_target, Set.mem_preimage]
  rfl

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The actual inverse has the exact ambient smooth formula on its target. -/
theorem levelChart_symm_val (d : SmoothRegularLevelData (I := I) f x)
    (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)))
    (hz : z ∈ d.levelChart.target) :
    (d.levelChart.symm z).val = (extChartAt I x.val).symm
      (d.coordinates.symm (0, d.modelEquiv.symm z)) := by
  have hz' := (d.mem_levelChart_target z).mp hz
  have heq := scalarLevelChart_symm_val f d.ambientChart d.ambientChart_first x
    (d.modelEquiv.symm z) hz'
  convert! heq using 1

end SmoothRegularLevelData
end CutoffRigidity
