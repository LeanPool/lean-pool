/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.LinearEquiv
import TauCeti.Geometry.Manifold.Immersion.ModelChange
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-! # Regular level manifolds in Euclidean coordinates -/

@[expose] public section

open Function
open scoped Manifold ContDiff

namespace CutoffRigidity.Riemann

/-- A Euclidean model of dimension `dim E - dim G` for the regular level. -/
abbrev LevelModel (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] : Type :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ G))

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {Ψ : M → G}

/-- The coordinate-vector model of the regular level before Euclidean transport. -/
abbrev LevelCoordinates (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] : Type :=
  Fin (Module.finrank ℝ E - Module.finrank ℝ G) → ℝ

/-- The identity on coordinates viewed with the Euclidean norm. -/
noncomputable def levelCoordinatesEquiv : LevelCoordinates E G ≃L[ℝ] LevelModel E G :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin (Module.finrank ℝ E - Module.finrank ℝ G) ↦ ℝ)).symm

/-- The regular-level coordinates with a Euclidean tangent model. -/
noncomputable abbrev euclideanLevelModel :
    ModelWithCorners ℝ (LevelModel E G) (LevelCoordinates E G) :=
  (𝓘(ℝ, LevelCoordinates E G)).transContinuousLinearEquiv
    (levelCoordinatesEquiv (E := E) (G := G))

/-- The regular level atlas in the coordinate-vector model. -/
@[instance_reducible] noncomputable def levelCoordinateAtlas (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : TauCeti.IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ 0) :
    ChartedSpace (LevelCoordinates E G) {z : M // Ψ z = 0} :=
  TauCeti.regularLevelChartedSpace (fun y _ ↦ (hΨ y).of_le (by simp)) hsub rfl

/-- Tau Ceti's regular-level atlas in the Euclidean inner product model. -/
@[instance_reducible] noncomputable def levelChartedSpace
    (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : TauCeti.IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ 0) :
    ChartedSpace (LevelModel E G) {z : M // Ψ z = 0} := by
  let := levelCoordinateAtlas hΨ hsub
  exact inferInstanceAs (ChartedSpace (LevelModel E G)
    (TauCeti.BoundarylessModel (euclideanLevelModel (E := E) (G := G)) {z : M // Ψ z = 0}))

theorem isManifold_level (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : TauCeti.IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ 0) :
    letI := levelChartedSpace hΨ hsub
    IsManifold 𝓘(ℝ, LevelModel E G) ∞ {z : M // Ψ z = 0} := by
  let := levelCoordinateAtlas hΨ hsub
  have : IsManifold 𝓘(ℝ, LevelCoordinates E G) ∞ {z : M // Ψ z = 0} :=
    TauCeti.isManifold_regularLevel (by simp) (fun y _ ↦ hΨ y) hsub rfl
  change IsManifold 𝓘(ℝ, LevelModel E G) ∞
    (TauCeti.BoundarylessModel (euclideanLevelModel (E := E) (G := G)) {z : M // Ψ z = 0})
  infer_instance

private theorem isSmoothEmbedding_level_val (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : TauCeti.IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ 0) :
    letI := levelChartedSpace hΨ hsub
    Manifold.IsSmoothEmbedding 𝓘(ℝ, LevelModel E G) 𝓘(ℝ, E) ∞
      (Subtype.val : {z : M // Ψ z = 0} → M) := by
  let L := {z : M // Ψ z = 0}
  let A := LevelCoordinates E G
  let B := LevelModel E G
  let := levelCoordinateAtlas hΨ hsub
  have : IsManifold 𝓘(ℝ, A) ∞ L :=
    TauCeti.isManifold_regularLevel (by simp) (fun y _ ↦ hΨ y) hsub rfl
  have hImm : Manifold.IsImmersionOfComplement G 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ (Subtype.val : L → M) :=
    TauCeti.isImmersionOfComplement_coe_regularLevel (by simp) (fun y _ ↦ hΨ y) hsub rfl
  let model := euclideanLevelModel (E := E) (G := G)
  let N := TauCeti.BoundarylessModel model L
  have : IsManifold 𝓘(ℝ, B) ∞ N := inferInstance
  let bridge : Diffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B) L N ∞ :=
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) 𝓘(ℝ, A) L
      (levelCoordinatesEquiv (E := E) (G := G))).trans
      (TauCeti.BoundarylessModel.diffeomorph model ∞)
  have hrange : (levelCoordinatesEquiv (E := E) (G := G)).symm '' Set.range 𝓘(ℝ, B) =
      Set.range 𝓘(ℝ, A) := by
    simp only [ModelWithCorners.range_eq_univ, Set.image_univ,
      (levelCoordinatesEquiv (E := E) (G := G)).symm.surjective.range_eq]
  have hTransport : Manifold.IsImmersionOfComplement G 𝓘(ℝ, B) 𝓘(ℝ, E) ∞
      ((Subtype.val : L → M) ∘ bridge.symm) := by
    intro x
    exact TauCeti.isImmersionAtOfComplement_comp_diffeomorph_of_image_range_eq
      (levelCoordinatesEquiv (E := E) (G := G)).symm hrange bridge.symm le_rfl
      (hImm (bridge.symm x))
  let := levelChartedSpace hΨ hsub
  change Manifold.IsSmoothEmbedding 𝓘(ℝ, B) 𝓘(ℝ, E) ∞ (fun x : N ↦ (x : L).val)
  refine ⟨hTransport.isImmersion.congr ?_, Topology.IsEmbedding.subtypeVal⟩
  funext x
  change Subtype.val ((ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) 𝓘(ℝ, A) L
      (levelCoordinatesEquiv (E := E) (G := G))).symm
    ((TauCeti.BoundarylessModel.diffeomorph model ∞).symm x)) = (x : L).val
  rw [TauCeti.BoundarylessModel.coe_diffeomorph_symm,
    TauCeti.BoundarylessModel.homeomorph_symm_apply]
  rfl

theorem contMDiff_level_val (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : TauCeti.IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ 0) :
    letI := levelChartedSpace hΨ hsub
    ContMDiff 𝓘(ℝ, LevelModel E G) 𝓘(ℝ, E) ∞ (Subtype.val : {z : M // Ψ z = 0} → M) := by
  let := levelChartedSpace hΨ hsub
  exact (isSmoothEmbedding_level_val hΨ hsub).isImmersion.contMDiff

theorem injective_mfderiv_level_val (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : TauCeti.IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ 0) :
    letI := levelChartedSpace hΨ hsub
    ∀ x : {z : M // Ψ z = 0}, Function.Injective
      (mfderiv 𝓘(ℝ, LevelModel E G) 𝓘(ℝ, E) (Subtype.val : {z : M // Ψ z = 0} → M) x) := by
  let := levelChartedSpace hΨ hsub
  exact (isSmoothEmbedding_level_val hΨ hsub).isImmersion.mfderiv_injective (by simp)

section Maps

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {P : Type*} [TopologicalSpace P] [ChartedSpace K P]

/-- A smooth ambient map with values in the level is smooth into the level manifold. -/
theorem contMDiff_into_level (hΨ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ Ψ)
    (hsub : TauCeti.IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, G) Ψ 0)
    {g : P → M} (hg : ContMDiff J 𝓘(ℝ, E) ∞ g) (hzero : ∀ z, Ψ (g z) = 0) :
    letI := levelChartedSpace hΨ hsub
    ContMDiff J 𝓘(ℝ, LevelModel E G) ∞
      (fun z ↦ (⟨g z, hzero z⟩ : {y : M // Ψ y = 0})) := by
  let := levelChartedSpace hΨ hsub
  exact (isSmoothEmbedding_level_val hΨ hsub).contMDiff_iff_comp.2 hg

end Maps

end CutoffRigidity.Riemann
