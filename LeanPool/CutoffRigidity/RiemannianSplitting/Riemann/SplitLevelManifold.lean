/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitLevelData

/-! # The `C^∞` manifold structure on the zero level of a vector-valued submersion -/

@[expose] public section
open Set
open scoped Manifold ContDiff Topology

namespace CutoffRigidity.Riemann

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {Ψ : M → G}

namespace LevelData
variable {y : {z : M // Ψ z = 0}}

/-- The ambient product chart. -/
noncomputable def ambientChart (d : LevelData E Ψ y) :=
  (chartAt E y.val).trans d.coordinates

omit [FiniteDimensional ℝ G] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem ambientChart_first (d : LevelData E Ψ y) (z : M) (hz : z ∈ d.ambientChart.source) :
    (d.ambientChart z).1 = Ψ z := by
  change (d.coordinates (chartAt E y.val z)).1 = Ψ z
  rw [d.first_eq, (chartAt E y.val).left_inv hz.1]

/-- The level chart with the common Euclidean model. -/
noncomputable def levelChart (d : LevelData E Ψ y) :
    OpenPartialHomeomorph {z : M // Ψ z = 0} (LevelModel E G) :=
  (vecLevelChart Ψ d.ambientChart d.ambientChart_first y).trans
    d.modelEquiv.toHomeomorph.toOpenPartialHomeomorph

omit [FiniteDimensional ℝ G] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem center_mem_levelChart_source (d : LevelData E Ψ y) : y ∈ d.levelChart.source := by
  refine ⟨?_, mem_univ _⟩
  exact ⟨mem_chart_source E y.val, d.center_mem⟩

omit [FiniteDimensional ℝ G] [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp] theorem levelChart_center (d : LevelData E Ψ y) : d.levelChart y = 0 := by
  change d.modelEquiv (d.coordinates (chartAt E y.val y.val)).2 = 0
  rw [d.center_eq, map_zero]

omit [FiniteDimensional ℝ G] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem levelChart_apply (d : LevelData E Ψ y) (z : {z : M // Ψ z = 0}) :
    d.levelChart z = d.modelEquiv (d.coordinates (chartAt E y.val z.val)).2 := by
  simp only [levelChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    vecLevelChart_apply, ambientChart, Homeomorph.toOpenPartialHomeomorph_apply,
    ContinuousLinearEquiv.coe_toHomeomorph]

omit [FiniteDimensional ℝ G] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem mem_levelChart_source (d : LevelData E Ψ y) (z : {z : M // Ψ z = 0}) :
    z ∈ d.levelChart.source ↔ z.val ∈ (chartAt E y.val).source ∧
      chartAt E y.val z.val ∈ d.coordinates.source := by
  simp only [levelChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ,
    vecLevelChart_source, Set.mem_preimage, ambientChart, Set.mem_inter_iff]

omit [FiniteDimensional ℝ G] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem mem_levelChart_target (d : LevelData E Ψ y) (w : LevelModel E G) :
    w ∈ d.levelChart.target ↔ ((0 : G), d.modelEquiv.symm w) ∈ d.ambientChart.target := by
  simp only [levelChart, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter,
    vecLevelChart_target, Set.mem_preimage]
  rfl

omit [FiniteDimensional ℝ G] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem levelChart_symm_val (d : LevelData E Ψ y) (w : LevelModel E G)
    (hw : w ∈ d.levelChart.target) :
    (d.levelChart.symm w).val =
      (chartAt E y.val).symm (d.coordinates.symm (0, d.modelEquiv.symm w)) := by
  have hw' := (d.mem_levelChart_target w).mp hw
  have heq := vecLevelChart_symm_val Ψ d.ambientChart d.ambientChart_first y
    (d.modelEquiv.symm w) hw'
  convert! heq using 1

/-- The ambient extension of the level coordinates. -/
noncomputable def forwardExtension (d : LevelData E Ψ y) (z : M) : LevelModel E G :=
  d.modelEquiv (d.coordinates (chartAt E y.val z)).2

/-- The ambient extension of the inverse level coordinates. -/
noncomputable def inverseExtension (d : LevelData E Ψ y) (w : LevelModel E G) : M :=
  (chartAt E y.val).symm (d.coordinates.symm (0, d.modelEquiv.symm w))

omit [FiniteDimensional ℝ G] in
theorem contMDiffAt_forwardExtension (d : LevelData E Ψ y) {z : M}
    (hz : z ∈ d.ambientChart.source) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, LevelModel E G) ∞ d.forwardExtension z := by
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E y.val) z :=
    (contMDiffOn_chart (I := 𝓘(ℝ, E)) (n := ∞) (x := y.val)).contMDiffAt
      ((chartAt E y.val).open_source.mem_nhds hz.1)
  have he : ContDiffAt ℝ ∞ d.coordinates (chartAt E y.val z) :=
    (d.smooth _ hz.2).contDiffAt (d.coordinates.open_source.mem_nhds hz.2)
  have hp : ContDiffAt ℝ ∞ (fun w ↦ d.modelEquiv (d.coordinates w).2) (chartAt E y.val z) :=
    d.modelEquiv.contDiff.contDiffAt.comp _ (contDiffAt_snd.comp _ he)
  exact hp.contMDiffAt.comp z hc

omit [FiniteDimensional ℝ G] in
theorem contMDiffAt_inverseExtension (d : LevelData E Ψ y) {w : LevelModel E G}
    (hw : w ∈ d.levelChart.target) :
    ContMDiffAt 𝓘(ℝ, LevelModel E G) 𝓘(ℝ, E) ∞ d.inverseExtension w := by
  have hw' := (d.mem_levelChart_target w).mp hw
  have hp : ((0 : G), d.modelEquiv.symm w) ∈ d.coordinates.target := hw'.1
  have hcSource : d.coordinates.symm (0, d.modelEquiv.symm w) ∈ (chartAt E y.val).target := hw'.2
  have he : ContDiffAt ℝ ∞ d.coordinates.symm (0, d.modelEquiv.symm w) :=
    (d.smooth_symm _ hp).contDiffAt (d.coordinates.open_target.mem_nhds hp)
  have ha : ContDiffAt ℝ ∞ (fun v : LevelModel E G ↦ ((0 : G), d.modelEquiv.symm v)) w :=
    contDiffAt_const.prodMk d.modelEquiv.symm.contDiff.contDiffAt
  have hcoord := he.comp w ha
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E y.val).symm
      (d.coordinates.symm (0, d.modelEquiv.symm w)) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞) (x := y.val)).contMDiffAt
      ((chartAt E y.val).open_target.mem_nhds hcSource)
  exact hc.comp w hcoord.contMDiffAt

omit [FiniteDimensional ℝ G] in
theorem contDiffAt_transition {y' : {z : M // Ψ z = 0}}
    (d : LevelData E Ψ y) (d' : LevelData E Ψ y') {w : LevelModel E G}
    (hw : w ∈ (d.levelChart.symm.trans d'.levelChart).source) :
    ContDiffAt ℝ ∞ (d.levelChart.symm.trans d'.levelChart) w := by
  have hw1 : w ∈ d.levelChart.target := hw.1
  have hw2 : d.levelChart.symm w ∈ d'.levelChart.source := hw.2
  have hident : d.inverseExtension w = (d.levelChart.symm w).val :=
    (d.levelChart_symm_val w hw1).symm
  have hy : d.inverseExtension w ∈ d'.ambientChart.source := by
    rw [hident]
    exact (d'.mem_levelChart_source _).mp hw2
  have hcomposition : ContDiffAt ℝ ∞ (d'.forwardExtension ∘ d.inverseExtension) w :=
    ((d'.contMDiffAt_forwardExtension hy).comp w (d.contMDiffAt_inverseExtension hw1)).contDiffAt
  have heq : (d.levelChart.symm.trans d'.levelChart : _ → _) =ᶠ[𝓝 w]
      (d'.forwardExtension ∘ d.inverseExtension) := by
    filter_upwards [(d.levelChart.symm.trans d'.levelChart).open_source.mem_nhds hw] with v hv
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, d'.levelChart_apply]
    rw [d.levelChart_symm_val v hv.1]
    rfl
  exact hcomposition.congr_of_eventuallyEq heq

omit [FiniteDimensional ℝ G] in
theorem contDiffOn_transition {y' : {z : M // Ψ z = 0}}
    (d : LevelData E Ψ y) (d' : LevelData E Ψ y') :
    ContDiffOn ℝ ∞ (d.levelChart.symm.trans d'.levelChart)
      (d.levelChart.symm.trans d'.levelChart).source :=
  fun _ hw ↦ (d.contDiffAt_transition d' hw).contDiffWithinAt

end LevelData

end CutoffRigidity.Riemann
