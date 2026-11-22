/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitDistance

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
noncomputable instance levelRiemannianBundle :
    RiemannianBundle (fun y : fr.Level =>
      TangentSpace 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) y) :=
  immersionPullbackRiemannianBundle (Subtype.val : fr.Level → M) fr.injective_mfderiv_level_val'

instance levelIsContMDiffRiemannianBundle :
    IsContMDiffRiemannianBundle 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) ∞
      (LevelModel F (EuclideanSpace ℝ (Fin k)))
      (fun y : fr.Level => TangentSpace 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) y) :=
  isContMDiffRiemannianBundle_immersionPullback_top (Subtype.val : fr.Level → M)
    fr.contMDiff_level_val' fr.injective_mfderiv_level_val'

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem norm_mfderiv_level_val (y : fr.Level)
    (v : TangentSpace 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) y) :
    ‖mfderiv 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F)
      (Subtype.val : fr.Level → M) y v‖ = ‖v‖ :=
  norm_mfderiv_immersionPullback (Subtype.val : fr.Level → M) fr.injective_mfderiv_level_val' y v

/-- The projection onto the level, as a map into the level manifold. -/
noncomputable def toLevel (x : M) : fr.Level := ⟨fr.retr x, fr.sv_retr x⟩

theorem contMDiff_toLevel :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) ∞ fr.toLevel :=
  contMDiff_into_level fr.contMDiff_sv fr.zero_isRegularValue fr.contMDiff_retr fr.sv_retr

theorem toLevel_val (y : fr.Level) : fr.toLevel y.val = y :=
  Subtype.ext (fr.retr_of_level y.property)

theorem norm_mfderiv_toLevel_le (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) fr.toLevel x v‖ ≤ ‖v‖ := by
  set u := mfderiv 𝓘(ℝ, F) 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) fr.toLevel x v with hu
  have h1 : ‖mfderiv 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F)
      (Subtype.val : fr.Level → M) (fr.toLevel x) u‖ = ‖u‖ := fr.norm_mfderiv_level_val _ u
  have hmd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k)))
      fr.toLevel x := (fr.contMDiff_toLevel.mdifferentiable (by simp)) x
  have hval : MDifferentiableAt 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F)
      (Subtype.val : fr.Level → M) (fr.toLevel x) :=
    (fr.contMDiff_level_val'.mdifferentiable (by simp)) _
  have h2 := mfderiv_comp x hval hmd
  have h3 : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v =
      mfderiv 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F)
        (Subtype.val : fr.Level → M) (fr.toLevel x) u := by
    have : (fun y : M => ((fr.toLevel y : fr.Level) : M)) = fr.retr := rfl
    have h4 : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x =
        (mfderiv 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F)
          (Subtype.val : fr.Level → M) (fr.toLevel x)).comp
          (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) fr.toLevel x) := h2
    exact congrArg (fun L => L v) h4
  have h5 : ‖mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v‖ ≤ ‖v‖ := by
    have := fr.norm_sq_split x v
    nlinarith [norm_nonneg (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) fr.retr x v), norm_nonneg v,
      sq_nonneg ‖fr.dsv x v‖]
  rw [← h1, ← h3]
  exact h5

instance levelIsRiemannianManifold :
    IsRiemannianManifold 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) fr.Level := by
  refine ⟨fun y y' => le_antisymm ?_ ?_⟩
  · -- `edist ≤ riemannianEDist`
    have h := riemannianEDist_le_riemannianEDist_of_norm_mfderiv_le_between
      (I := 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k)))) (J := 𝓘(ℝ, F))
      (φ := (Subtype.val : fr.Level → M))
      (fr.contMDiff_level_val'.of_le (by simp))
      (fun z v => (fr.norm_mfderiv_level_val z v).le) y y'
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, F))] at h
    exact h
  · have h := riemannianEDist_le_edist_of_norm_mfderiv_le_between
      (I := 𝓘(ℝ, F)) (J := 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))))
      (φ := fr.toLevel) (fr.contMDiff_toLevel.of_le (by simp)) fr.norm_mfderiv_toLevel_le y.val
          y'.val
    rw [fr.toLevel_val, fr.toLevel_val] at h
    exact h

end Frame

end CutCur
