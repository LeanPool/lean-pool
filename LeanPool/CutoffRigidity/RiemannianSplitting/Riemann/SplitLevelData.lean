/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitLevelEuclid

/-! # `C^∞` level charts of a vector-valued submersion on a manifold

`N = {y : M // Ψ y = 0}` for a smooth `Ψ : M → G` whose differential is onto at every point of `N`.
Charts: adapted coordinates (implicit function theorem) of the ambient chart, restricted to `N`.
-/

@[expose] public section
open Set
open scoped Manifold ContDiff Topology

namespace CutoffRigidity.Riemann

section Topological

variable {A G W : Type*} [TopologicalSpace A] [TopologicalSpace W] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- Restrict a product chart `(Ψ, ·)` to the zero level of `Ψ`. -/
noncomputable def vecLevelChart (Ψ : A → G) (e : OpenPartialHomeomorph A (G × W))
    (hfirst : ∀ x ∈ e.source, (e x).1 = Ψ x) (x₀ : {x : A // Ψ x = 0}) :
    OpenPartialHomeomorph {x : A // Ψ x = 0} W := by
  classical
  let inverse : W → {x : A // Ψ x = 0} := fun y ↦
    if hy : (0, y) ∈ e.target then
      ⟨e.symm (0, y), by
        rw [← hfirst _ (e.map_target hy), e.right_inv hy]⟩
    else x₀
  have hinv (y : W) (hy : (0, y) ∈ e.target) :
      (inverse y).val = e.symm (0, y) := by simp only [inverse, dite_eq_left hy]
  have hpair (x : {x : A // Ψ x = 0}) (hx : x.val ∈ e.source) : (0, (e x.val).2) = e x.val := by
    ext
    · exact (hfirst x.val hx).trans x.property |>.symm
    · rfl
  refine
    { toFun := fun x ↦ (e x.val).2
      invFun := inverse
      source := Subtype.val ⁻¹' e.source
      target := (fun y : W ↦ ((0 : G), y)) ⁻¹' e.target
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := e.open_target.preimage (continuous_const.prodMk continuous_id) }
  · intro x hx
    change (0, (e x.val).2) ∈ e.target
    rw [hpair x hx]
    exact e.map_source hx
  · intro y hy
    change (inverse y).val ∈ e.source
    rw [hinv y hy]
    exact e.map_target hy
  · intro x hx
    apply Subtype.ext
    have hy : (0, (e x.val).2) ∈ e.target := by rw [hpair x hx]; exact e.map_source hx
    rw [hinv _ hy, hpair x hx]
    exact e.left_inv hx
  · intro y hy
    rw [hinv y hy, e.right_inv hy]
  · exact continuous_snd.comp_continuousOn
      (e.continuousOn.comp continuous_subtype_val.continuousOn fun _ hx ↦ hx)
  · have inducing : Topology.IsInducing
        (Subtype.val : {x : A // Ψ x = 0} → A) := ⟨rfl⟩
    apply (inducing.continuousOn_iff (f := inverse)).mpr
    exact (e.continuousOn_symm.comp
      (continuous_const.prodMk continuous_id).continuousOn fun _ hy ↦ hy).congr
      (fun y hy ↦ hinv y hy)

omit [NormedSpace ℝ G] in
@[simp] theorem vecLevelChart_apply (Ψ : A → G) (e : OpenPartialHomeomorph A (G × W))
    (hfirst : ∀ x ∈ e.source, (e x).1 = Ψ x) (x₀ : {x : A // Ψ x = 0})
    (x : {x : A // Ψ x = 0}) : vecLevelChart Ψ e hfirst x₀ x = (e x.val).2 := rfl

omit [NormedSpace ℝ G] in
@[simp] theorem vecLevelChart_source (Ψ : A → G) (e : OpenPartialHomeomorph A (G × W))
    (hfirst : ∀ x ∈ e.source, (e x).1 = Ψ x) (x₀ : {x : A // Ψ x = 0}) :
    (vecLevelChart Ψ e hfirst x₀).source = Subtype.val ⁻¹' e.source := rfl

omit [NormedSpace ℝ G] in
@[simp] theorem vecLevelChart_target (Ψ : A → G) (e : OpenPartialHomeomorph A (G × W))
    (hfirst : ∀ x ∈ e.source, (e x).1 = Ψ x) (x₀ : {x : A // Ψ x = 0}) :
    (vecLevelChart Ψ e hfirst x₀).target = (fun y : W ↦ ((0 : G), y)) ⁻¹' e.target := rfl

omit [NormedSpace ℝ G] in
theorem vecLevelChart_symm_val (Ψ : A → G) (e : OpenPartialHomeomorph A (G × W))
    (hfirst : ∀ x ∈ e.source, (e x).1 = Ψ x) (x₀ : {x : A // Ψ x = 0})
    (y : W) (hy : ((0 : G), y) ∈ e.target) :
    ((vecLevelChart Ψ e hfirst x₀).symm y).val = e.symm (0, y) := by
  simp [vecLevelChart, OpenPartialHomeomorph.coe_mk_symm, hy]

end Topological

section Data

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The model of the level: Euclidean space of dimension `dim E - dim G`. -/
abbrev LevelModel (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] : Type :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ G))

/-- The Euclidean representative of `Ψ` in the chart at `y`. -/
noncomputable abbrev chartRep (Ψ : M → G) (y : M) : E → G :=
  Ψ ∘ (chartAt E y).symm

/-- Adapted coordinates in the chart at `y`, with their `C^∞` smoothness witnesses. -/
structure LevelData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] (Ψ : M → G) (y : {z : M // Ψ z = 0}) where
  /-- The adapted chart on the model space, with the level function in the first component. -/
  coordinates : OpenPartialHomeomorph E
    (G × (fderiv ℝ (chartRep Ψ y.val) (chartAt E y.val y.val)).ker)
  center_mem : chartAt E y.val y.val ∈ coordinates.source
  source_subset : coordinates.source ⊆ (chartAt E y.val).target
  center_eq : coordinates (chartAt E y.val y.val) = (0, 0)
  first_eq : ∀ z, (coordinates z).1 = Ψ ((chartAt E y.val).symm z)
  smooth : ContDiffOn ℝ ∞ coordinates coordinates.source
  smooth_symm : ContDiffOn ℝ ∞ coordinates.symm coordinates.target
  /-- The identification of the derivative kernel with the Euclidean level model. -/
  modelEquiv : (fderiv ℝ (chartRep Ψ y.val) (chartAt E y.val y.val)).ker ≃L[ℝ] LevelModel E G

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- Smoothness of the chart representative on the chart target. -/
theorem contDiffOn_chartRep {Ψ : M → G} (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ) (y : M) :
    ContDiffOn ℝ ∞ (chartRep Ψ y) (chartAt E y).target := by
  have h := (hΨ.contMDiffOn (s := univ)).comp (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞) (x
      := y))
    (fun _ _ => mem_univ _)
  exact h.contDiffOn

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- Surjectivity of the chart-representative differential from that of `mfderiv Ψ`. -/
theorem surjective_fderiv_chartRep {Ψ : M → G} (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ) (y : M)
    (hsub : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ y)) :
    Function.Surjective (fderiv ℝ (chartRep Ψ y) (chartAt E y y)) := by
  set c := chartAt E y with hc
  have hy : y ∈ c.source := mem_chart_source E y
  have hΨy : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ y := (hΨ y).mdifferentiableAt (by simp)
  have hrep : DifferentiableAt ℝ (chartRep Ψ y) (c y) := by
    have := contDiffOn_chartRep hΨ y
    exact ((this.contDiffAt (c.open_target.mem_nhds (c.map_source hy))).differentiableAt (by simp))
  have hcd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) c y :=
    ((contMDiffOn_chart (I := 𝓘(ℝ, E)) (n := ∞) (x := y)).contMDiffAt
      (c.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
  have heq : Ψ =ᶠ[𝓝 y] (chartRep Ψ y) ∘ c := by
    filter_upwards [c.open_source.mem_nhds hy] with z hz
    change Ψ z = Ψ (c.symm (c z))
    rw [c.left_inv hz]
  have h1 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ y =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (chartRep Ψ y) (c y)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c y) := by
    rw [heq.mfderiv_eq]
    exact mfderiv_comp y hrep.mdifferentiableAt hcd
  rw [h1] at hsub
  have h2 : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (chartRep Ψ y) (c y)) :=
    Function.Surjective.of_comp hsub
  rwa [mfderiv_eq_fderiv] at h2

/-- Existence of adapted coordinates. -/
theorem nonempty_levelData {Ψ : M → G} (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (y : {z : M // Ψ z = 0})
    (hsub : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ y.val)) :
    Nonempty (LevelData E Ψ y) := by
  set c := chartAt E y.val with hc
  have hy : y.val ∈ c.source := mem_chart_source E y.val
  have hsurj := surjective_fderiv_chartRep hΨ y.val hsub
  obtain ⟨e, he, heT, hecenter, hefirst, hsm, hsm'⟩ := exists_contDiff_regular_coordinates
    (chartRep Ψ y.val) c.open_target (contDiffOn_chartRep hΨ y.val) (c.map_source hy) hsurj
  let D := fderiv ℝ (chartRep Ψ y.val) (c y.val)
  have hdim : Module.finrank ℝ D.ker = Module.finrank ℝ (LevelModel E G) := by
    have hrank := D.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj] at hrank
    have : Module.finrank ℝ G + Module.finrank ℝ D.ker = Module.finrank ℝ E := by
      simpa using hrank
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    omega
  refine ⟨{ coordinates := e
            center_mem := he
            source_subset := heT
            center_eq := ?_
            first_eq := ?_
            smooth := hsm
            smooth_symm := hsm'
            modelEquiv := ContinuousLinearEquiv.ofFinrankEq hdim }⟩
  · rw [hecenter]
    change (Ψ (c.symm (c y.val)), (0 : (fderiv ℝ (chartRep Ψ y.val) (c y.val)).ker)) = (0, 0)
    rw [c.left_inv hy, y.property]
  · intro z
    rw [hefirst]
    rfl

end Data

end CutoffRigidity.Riemann
