/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitIsometry
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitProduct
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
import TauCeti.Geometry.Manifold.Riemannian.Distance

/-! # The Riemannian structure of the level `N` and `IsRiemannianManifold`

`N = {s = 0}` with the metric pulled back by the inclusion; its extended distance (the restriction
of the one of `M`) is the Riemannian distance of `N`.
-/

@[expose] public section

open Bundle MeasureTheory Set Filter Manifold
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

namespace Frame

open CutoffRigidity CutoffRigidity.Riemann

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] {k : ℕ} (fr : Frame F M k)

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem injective_mfderiv_level_val' :
    ∀ y : fr.Level, Function.Injective
      (mfderiv 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F)
        (Subtype.val : fr.Level → M) y) :=
  injective_mfderiv_level_val fr.contMDiff_sv fr.zero_isRegularValue

/-- The induced Riemannian metric on the level. -/
noncomputable def levelRiemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) ∞
      (LevelModel F (EuclideanSpace ℝ (Fin k)))
      (fun y : fr.Level ↦ TangentSpace 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) y) := by
  let metric : ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
      (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x) :=
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
  exact metric.pullback (Subtype.val : fr.Level → M)
    (by simpa using fr.contMDiff_level_val')
    fr.injective_mfderiv_level_val'

noncomputable instance levelRiemannianBundle :
    RiemannianBundle (fun y : fr.Level =>
      TangentSpace 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) y) :=
  ⟨fr.levelRiemannianMetric.toRiemannianMetric⟩

instance levelIsContMDiffRiemannianBundle :
    IsContMDiffRiemannianBundle 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) ∞
      (LevelModel F (EuclideanSpace ℝ (Fin k)))
      (fun y : fr.Level => TangentSpace 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) y) := by
  infer_instance

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem norm_mfderiv_level_val (y : fr.Level)
    (v : TangentSpace 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) y) :
    ‖mfderiv 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F)
      (Subtype.val : fr.Level → M) y v‖ = ‖v‖ := by
  let w := mfderiv 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F)
    (Subtype.val : fr.Level → M) y v
  have h : inner ℝ w w = inner ℝ v v := by
    change inner ℝ w w = fr.levelRiemannianMetric.inner y v v
    rw [levelRiemannianMetric, ContMDiffRiemannianMetric.pullback_inner,
      ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
    rfl
  simpa only [norm_eq_sqrt_real_inner] using congrArg Real.sqrt h

/-- The differential of the projection onto the level. -/
noncomputable abbrev dpi (x : M) :
    TangentSpace 𝓘(ℝ, F) x →L[ℝ]
      TangentSpace 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) (fr.toLevel x) :=
  mfderiv 𝓘(ℝ, F) 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) fr.toLevel x

theorem mdiff_toLevel (x : M) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) fr.toLevel x :=
  (fr.contMDiff_toLevel.mdifferentiable (by simp)) x

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem mdiff_level_val (y : fr.Level) :
    MDifferentiableAt 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F)
      (Subtype.val : fr.Level → M) y :=
  (fr.contMDiff_level_val'.mdifferentiable (by simp)) y

/-- `d val ∘ dπ = d retr`. -/
theorem dval_dpi (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    mfderiv 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F)
        (Subtype.val : fr.Level → M) (fr.toLevel x) (fr.dpi x v) =
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v := by
  have h2 := mfderiv_comp x (fr.mdiff_level_val (fr.toLevel x)) (fr.mdiff_toLevel x)
  have h4 : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x =
      (mfderiv 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F)
        (Subtype.val : fr.Level → M) (fr.toLevel x)).comp (fr.dpi x) := h2
  exact (congrArg (fun L => L v) h4).symm

theorem norm_dpi (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    ‖fr.dpi x v‖ = ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v‖ := by
  rw [← fr.dval_dpi]
  exact (fr.norm_mfderiv_level_val (fr.toLevel x) (fr.dpi x v)).symm

theorem norm_mfderiv_toLevel_le (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) fr.toLevel x v‖ ≤ ‖v‖ := by
  change ‖fr.dpi x v‖ ≤ ‖v‖
  rw [fr.norm_dpi]
  exact fr.norm_mfderiv_retr_le x v

instance levelIsRiemannianManifold :
    IsRiemannianManifold 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) fr.Level := by
  have hOne : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by simp
  refine ⟨fun y y' ↦ le_antisymm ?_ ?_⟩
  · have h := TauCeti.Manifold.riemannianEDist_le_mul
      (fr.contMDiff_level_val'.of_le hOne) (C := 1) one_ne_zero
      (fun z v ↦ by simpa only [NNReal.coe_one, one_mul] using
        (fr.norm_mfderiv_level_val z v).le) y y'
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, F))] at h
    change edist y.val y'.val ≤ _
    simpa only [ENNReal.coe_one, one_mul] using h
  · have h := TauCeti.Manifold.riemannianEDist_le_mul
      (fr.contMDiff_toLevel.of_le hOne) (C := 1) one_ne_zero
      (fun z v ↦ by simpa only [NNReal.coe_one, one_mul] using fr.norm_mfderiv_toLevel_le z v)
      y.val y'.val
    rw [fr.toLevel_val, fr.toLevel_val, ← IsRiemannianManifold.out (I := 𝓘(ℝ, F))] at h
    change _ ≤ edist y.val y'.val
    simpa only [ENNReal.coe_one, one_mul] using h

end Frame

end CutCur
