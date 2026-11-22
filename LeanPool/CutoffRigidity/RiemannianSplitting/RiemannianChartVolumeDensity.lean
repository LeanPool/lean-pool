/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartMetric
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # The genuine Riemannian chart volume density

The density is the norm determinant of the actual inverse tangent chart.
Its square is the actual Gram determinant; positivity and regularity are
proved from the original Riemannian metric and genuine chart inverses.
-/
@[expose] public section
namespace CutoffRigidity
open Bundle Set
open scoped Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The square root of the determinant of the metric in the chart frame. -/
noncomputable def chartRiemannianVolumeDensity (x₀ : M) (z : E) : ℝ :=
  (chartFrameCLM (I := I) x₀ ((extChartAt I x₀).symm z)).toLinearMap.normDet

/-- The Gram matrix of the chart frame formed from an orthonormal model basis. -/
noncomputable def chartRiemannianGram (x₀ : M) (z : E) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun i j => chartMetric (I := I) x₀ z
    (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [BoundarylessManifold I M] in
theorem chartRiemannianVolumeDensity_nonneg (x₀ : M) (z : E) :
    0 ≤ chartRiemannianVolumeDensity (I := I) x₀ z := LinearMap.normDet_nonneg _

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [FiniteDimensional ℝ E]
  [BoundarylessManifold I M]
  [RiemannianBundle fun x : M ↦ TangentSpace I x] in
theorem chartFrameCLM_injective_of_mem_target (x₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    Function.Injective (chartFrameCLM (I := I) x₀ ((extChartAt I x₀).symm z)) := by
  let y := (extChartAt I x₀).symm z
  have hy : y ∈ (chartAt H x₀).source := by
    simpa only [y,extChartAt_source] using (extChartAt I x₀).map_target hz
  have hy' : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hy
  intro u v huv
  have hh := congrArg ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y) huv
  change (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y
    ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y u) =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y v) at hh
  simpa only [(trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL hy'] using hh

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [BoundarylessManifold I M] in
theorem chartRiemannianVolumeDensity_pos (x₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    0 < chartRiemannianVolumeDensity (I := I) x₀ z := by
  have hn : chartRiemannianVolumeDensity (I := I) x₀ z ≠ 0 := by
    have hk := LinearMap.ker_eq_bot.mpr (chartFrameCLM_injective_of_mem_target x₀ hz)
    intro hzero
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp hzero) hk
  exact lt_of_le_of_ne (chartRiemannianVolumeDensity_nonneg x₀ z) (Ne.symm hn)

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [BoundarylessManifold I M] in
/-- The actual metric determinant gives exactly the square of the genuine
Jacobian volume density. -/
theorem chartRiemannianVolumeDensity_sq (x₀ : M) (z : E) :
    chartRiemannianVolumeDensity (I := I) x₀ z ^ 2 = (chartRiemannianGram (I := I) x₀ z).det := by
  have hh := LinearMap.normDet_sq_eq_det_gram
    (chartFrameCLM (I := I) x₀ ((extChartAt I x₀).symm z)).toLinearMap
    (stdOrthonormalBasis ℝ E)
  convert! hh using 1

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [BoundarylessManifold I M] in
theorem chartRiemannianVolumeDensity_eq_sqrt (x₀ : M) (z : E) :
    chartRiemannianVolumeDensity (I := I) x₀ z =
      Real.sqrt ((chartRiemannianGram (I := I) x₀ z).det) := by
  rw [← chartRiemannianVolumeDensity_sq]
  exact (Real.sqrt_sq (chartRiemannianVolumeDensity_nonneg x₀ z)).symm

/-- The genuine volume density is C¹ at every chart center. -/
theorem contDiffAt_chartRiemannianVolumeDensity (x₀ : M) :
    ContDiffAt ℝ 1 (chartRiemannianVolumeDensity (I := I) x₀) (extChartAt I x₀ x₀) := by
  have hEntry (i j : Fin (Module.finrank ℝ E)) :
      ContDiffAt ℝ 1 (fun z => chartRiemannianGram (I := I) x₀ z i j) (extChartAt I x₀ x₀) :=
    ((contDiffAt_chartMetric (I := I) x₀).clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hDet : ContDiffAt ℝ 1 (fun z => (chartRiemannianGram (I := I) x₀ z).det)
      (extChartAt I x₀ x₀) := by
    classical
    simp only [Matrix.det_apply]
    fun_prop
  have hPos : 0 < (chartRiemannianGram (I := I) x₀ (extChartAt I x₀ x₀)).det := by
    rw [← chartRiemannianVolumeDensity_sq]
    exact sq_pos_of_pos (chartRiemannianVolumeDensity_pos x₀ (mem_extChartAt_target x₀))
  have hh := hDet.sqrt hPos.ne'
  convert! hh using 1
  funext z
  exact chartRiemannianVolumeDensity_eq_sqrt x₀ z

end CutoffRigidity
