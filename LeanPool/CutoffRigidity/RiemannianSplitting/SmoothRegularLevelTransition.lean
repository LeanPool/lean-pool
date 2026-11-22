/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.SmoothRegularLevelData

/-! # Actual smooth extensions of regular-level coordinates -/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

namespace SmoothRegularLevelData
variable {f : M → ℝ} {x : {y : M // f y = 0}}

/-- The actual ambient extension of the level coordinates. -/
noncomputable def forwardExtension (d : SmoothRegularLevelData (I := I) f x) (y : M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
  d.modelEquiv (d.coordinates (extChartAt I x.val y)).2

/-- The actual ambient extension of the inverse level coordinates. -/
noncomputable def inverseExtension (d : SmoothRegularLevelData (I := I) f x)
    (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) : M :=
  (extChartAt I x.val).symm (d.coordinates.symm (0, d.modelEquiv.symm z))

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- Smoothness of the actual forward extension follows from the actual
ambient chart and the actual IFT coordinate map. -/
theorem contMDiffAt_forwardExtension (d : SmoothRegularLevelData (I := I) f x)
    {y : M} (hy : y ∈ d.ambientChart.source) :
    ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) 2
      d.forwardExtension y := by
  have hchartSource : y ∈ (chartAt H x.val).source := by
    simpa only [OpenPartialHomeomorph.symm_target, boundarylessExtChart, extChartAt_source] using
        hy.1
  have hc : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I x.val) y :=
    contMDiffAt_extChartAt' hchartSource
  have he : ContDiffAt ℝ 2 d.coordinates (extChartAt I x.val y) :=
    (d.smooth _ hy.2).contDiffAt (d.coordinates.open_source.mem_nhds hy.2)
  have hp : ContDiffAt ℝ 2 (fun z ↦ d.modelEquiv (d.coordinates z).2)
      (extChartAt I x.val y) :=
    d.modelEquiv.contDiff.contDiffAt.comp _ (contDiffAt_snd.comp _ he)
  exact hp.contMDiffAt.comp y hc

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- Smoothness of the actual inverse extension follows from the actual IFT
inverse and the actual inverse manifold chart, on the actual level target. -/
theorem contMDiffAt_inverseExtension (d : SmoothRegularLevelData (I := I) f x)
    {z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))}
    (hz : z ∈ d.levelChart.target) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) I 2
      d.inverseExtension z := by
  have hz' := (d.mem_levelChart_target z).mp hz
  have hp : (0, d.modelEquiv.symm z) ∈ d.coordinates.target := hz'.1
  have hcSource : d.coordinates.symm (0, d.modelEquiv.symm z) ∈
      (extChartAt I x.val).target := hz'.2
  have he : ContDiffAt ℝ 2 d.coordinates.symm (0, d.modelEquiv.symm z) :=
    (d.smooth_symm _ hp).contDiffAt (d.coordinates.open_target.mem_nhds hp)
  have ha : ContDiffAt ℝ 2 (fun w ↦ ((0 : ℝ), d.modelEquiv.symm w)) z :=
    contDiffAt_const.prodMk d.modelEquiv.symm.contDiff.contDiffAt
  have hcoord := he.comp z ha
  have hc : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I x.val).symm
      (d.coordinates.symm (0, d.modelEquiv.symm z)) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := 2) x.val _ hcSource).contMDiffAt
      ((isOpen_extChartAt_target_of_boundarylessManifold (I := I) x.val).mem_nhds hcSource)
  exact hc.comp z hcoord.contMDiffAt

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The actual constructed level-chart transitions are `C²`; this is derived
from the two actual ambient smooth extensions and their exact inverse formulas. -/
theorem contDiffAt_transition {x' : {y : M // f y = 0}}
    (d : SmoothRegularLevelData (I := I) f x)
    (d' : SmoothRegularLevelData (I := I) f x')
    {z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))}
    (hz : z ∈ (d.levelChart.symm.trans d'.levelChart).source) :
    ContDiffAt ℝ 2 (d.levelChart.symm.trans d'.levelChart) z := by
  have hz1 : z ∈ d.levelChart.target := hz.1
  have hz2 : d.levelChart.symm z ∈ d'.levelChart.source := hz.2
  have hident : d.inverseExtension z = (d.levelChart.symm z).val :=
    (d.levelChart_symm_val z hz1).symm
  have hy : d.inverseExtension z ∈ d'.ambientChart.source := by
    rw [hident]
    exact (d'.mem_levelChart_source _).mp hz2
  have hcomposition : ContDiffAt ℝ 2 (d'.forwardExtension ∘ d.inverseExtension) z :=
    ((d'.contMDiffAt_forwardExtension hy).comp z (d.contMDiffAt_inverseExtension hz1)).contDiffAt
  have heq : (d.levelChart.symm.trans d'.levelChart : _ → _) =ᶠ[𝓝 z]
      (d'.forwardExtension ∘ d.inverseExtension) := by
    filter_upwards [(d.levelChart.symm.trans d'.levelChart).open_source.mem_nhds hz] with w hw
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, d'.levelChart_apply]
    rw [d.levelChart_symm_val w hw.1]
    rfl
  exact hcomposition.congr_of_eventuallyEq heq

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- Smooth compatibility holds throughout the actual transition domain. -/
theorem contDiffOn_transition {x' : {y : M // f y = 0}}
    (d : SmoothRegularLevelData (I := I) f x)
    (d' : SmoothRegularLevelData (I := I) f x') :
    ContDiffOn ℝ 2 (d.levelChart.symm.trans d'.levelChart)
      (d.levelChart.symm.trans d'.levelChart).source :=
  fun _ hz ↦ (d.contDiffAt_transition d' hz).contDiffWithinAt


end SmoothRegularLevelData
end CutoffRigidity
