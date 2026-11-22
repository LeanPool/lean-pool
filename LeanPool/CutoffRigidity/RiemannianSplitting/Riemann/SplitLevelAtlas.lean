/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitLevelManifold

/-! # Atlas, smoothness of the inclusion and of maps into the level -/

@[expose] public section
open Set
open scoped Manifold ContDiff Topology

namespace CutoffRigidity.Riemann

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {Ψ : M → G}

/-- Chosen adapted coordinates. -/
noncomputable def levelData (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : ∀ y : M, Ψ y = 0 → Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ y))
    (y : {z : M // Ψ z = 0}) : LevelData E Ψ y :=
  Classical.choice (nonempty_levelData hΨ y (hsub y.val y.property))

/-- The atlas of the level. -/
@[instance_reducible] noncomputable def levelChartedSpace (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : ∀ y : M, Ψ y = 0 → Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ y)) :
    ChartedSpace (LevelModel E G) {z : M // Ψ z = 0} where
  atlas := range (fun y => (levelData hΨ hsub y).levelChart)
  chartAt y := (levelData hΨ hsub y).levelChart
  mem_chart_source y := (levelData hΨ hsub y).center_mem_levelChart_source
  chart_mem_atlas y := ⟨y, rfl⟩

theorem isManifold_level (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : ∀ y : M, Ψ y = 0 → Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ y)) :
    letI := levelChartedSpace hΨ hsub
    IsManifold 𝓘(ℝ, LevelModel E G) ∞ {z : M // Ψ z = 0} := by
  let := levelChartedSpace hΨ hsub
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, preimage_id, range_id, inter_univ] using
    (levelData hΨ hsub x).contDiffOn_transition (levelData hΨ hsub x')

theorem contMDiff_level_val (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : ∀ y : M, Ψ y = 0 → Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ y)) :
    letI := levelChartedSpace hΨ hsub
    ContMDiff 𝓘(ℝ, LevelModel E G) 𝓘(ℝ, E) ∞ (Subtype.val : {z : M // Ψ z = 0} → M) := by
  let := levelChartedSpace hΨ hsub
  intro x
  rw [contMDiffAt_iff_source]
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    range_id, contMDiffWithinAt_univ]
  let d := levelData hΨ hsub x
  change ContMDiffAt 𝓘(ℝ, LevelModel E G) 𝓘(ℝ, E) ∞
    (fun w ↦ (d.levelChart.symm w).val) (d.levelChart x)
  have hz := d.levelChart.map_source d.center_mem_levelChart_source
  have hi := d.contMDiffAt_inverseExtension hz
  have hi' : ContMDiffAt 𝓘(ℝ, LevelModel E G) 𝓘(ℝ, E) ∞ (fun w ↦ d.inverseExtension w)
      (d.levelChart x) := hi
  apply hi'.congr_of_eventuallyEq
  filter_upwards [d.levelChart.open_target.mem_nhds hz] with w hw'
  rw [d.levelChart_symm_val w hw']
  rfl

theorem injective_mfderiv_level_val (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : ∀ y : M, Ψ y = 0 → Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ y)) :
    letI := levelChartedSpace hΨ hsub
    ∀ x : {z : M // Ψ z = 0}, Function.Injective
      (mfderiv 𝓘(ℝ, LevelModel E G) 𝓘(ℝ, E) (Subtype.val : {z : M // Ψ z = 0} → M) x) := by
  let := levelChartedSpace hΨ hsub
  have := isManifold_level hΨ hsub
  intro x
  let J := 𝓘(ℝ, LevelModel E G)
  let d := levelData hΨ hsub x
  let inc : {z : M // Ψ z = 0} → M := Subtype.val
  have hinc : MDifferentiableAt J 𝓘(ℝ, E) inc x :=
    ((contMDiff_level_val hΨ hsub) x).mdifferentiableAt (by simp)
  have hy : x.val ∈ d.ambientChart.source :=
    (d.mem_levelChart_source x).mp d.center_mem_levelChart_source
  have hforward := (d.contMDiffAt_forwardExtension hy).mdifferentiableAt (by simp)
  have hfun : d.forwardExtension ∘ inc = (extChartAt J x : _ → _) := by
    funext z
    simp only [extChartAt_coe]
    change d.forwardExtension z.val = d.levelChart z
    exact (d.levelChart_apply z).symm
  have hderiv := mfderiv_congr (I := J) (I' := J) (x := x) hfun
  rw [mfderiv_comp x hforward hinc] at hderiv
  have hinvert := isInvertible_mfderiv_extChartAt (I := J) (mem_extChartAt_source x)
  intro v w hvw
  apply hinvert.injective
  rw [← hderiv]
  change (mfderiv 𝓘(ℝ, E) J d.forwardExtension x.val)
      ((mfderiv J 𝓘(ℝ, E) inc x) v) =
    (mfderiv 𝓘(ℝ, E) J d.forwardExtension x.val) ((mfderiv J 𝓘(ℝ, E) inc x) w)
  rw [hvw]

section Maps
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {P : Type*} [TopologicalSpace P] [ChartedSpace K P]

/-- A smooth ambient map with values in the level is smooth into the level manifold. -/
theorem contMDiff_into_level (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : ∀ y : M, Ψ y = 0 → Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ y))
    {g : P → M} (hg : ContMDiff J 𝓘(ℝ, E) ∞ g) (hzero : ∀ z, Ψ (g z) = 0) :
    letI := levelChartedSpace hΨ hsub
    ContMDiff J 𝓘(ℝ, LevelModel E G) ∞
      (fun z ↦ (⟨g z, hzero z⟩ : {y : M // Ψ y = 0})) := by
  let := levelChartedSpace hΨ hsub
  let intoLevel : P → {y : M // Ψ y = 0} := fun z ↦ ⟨g z, hzero z⟩
  have hcont : Continuous intoLevel := hg.continuous.subtype_mk hzero
  intro z
  rw [contMDiffAt_iff_target]
  refine ⟨hcont.continuousAt, ?_⟩
  let d := levelData hΨ hsub (intoLevel z)
  have hy : g z ∈ d.ambientChart.source :=
    (d.mem_levelChart_source (intoLevel z)).mp d.center_mem_levelChart_source
  have hcomp := (d.contMDiffAt_forwardExtension hy).comp z (hg z)
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
  change ContMDiffAt J 𝓘(ℝ, LevelModel E G) ∞ (d.levelChart ∘ intoLevel) z
  have heq : d.levelChart ∘ intoLevel = d.forwardExtension ∘ g := by
    funext y
    exact d.levelChart_apply (intoLevel y)
  rw [heq]
  exact hcomp

end Maps

end CutoffRigidity.Riemann
