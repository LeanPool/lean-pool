/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitAction
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitLevelAtlas
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitMetric

/-! # The smooth product decomposition `M ≃ₘ^∞ ℝ^k × N` of a frame -/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

namespace Frame

open CutoffRigidity.Riemann

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] {k : ℕ} (fr : Frame F M k)

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem hsub : ∀ y : M, fr.sv y = 0 →
    Function.Surjective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) fr.sv y) :=
  fun y _ => fr.surjective_mfderiv_sv y

/-- Charts on the zero level. -/
noncomputable instance levelCharted :
    ChartedSpace (LevelModel F (EuclideanSpace ℝ (Fin k))) fr.Level :=
  levelChartedSpace fr.contMDiff_sv fr.hsub

instance levelIsManifold :
    IsManifold 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) ∞ fr.Level :=
  isManifold_level fr.contMDiff_sv fr.hsub

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem contMDiff_level_val' :
    ContMDiff 𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k))) 𝓘(ℝ, F) ∞
      (Subtype.val : fr.Level → M) :=
  contMDiff_level_val fr.contMDiff_sv fr.hsub

/-- The smooth product decomposition. -/
noncomputable def splitEquiv :
    M ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, EuclideanSpace ℝ (Fin k)).prod
      𝓘(ℝ, LevelModel F (EuclideanSpace ℝ (Fin k)))⟯ EuclideanSpace ℝ (Fin k) × fr.Level where
  toFun x := (fr.sv x, ⟨fr.retr x, fr.sv_retr x⟩)
  invFun p := fr.comp (List.finRange k) p.1 p.2.val
  left_inv x := fr.comp_retr x
  right_inv p := by
    obtain ⟨t, y, hy⟩ := p
    refine Prod.ext (fr.sv_comp t y hy) (Subtype.ext ?_)
    exact fr.retr_comp t y hy
  contMDiff_toFun :=
    fr.contMDiff_sv.prodMk (contMDiff_into_level fr.contMDiff_sv fr.hsub fr.contMDiff_retr
      fr.sv_retr)
  contMDiff_invFun :=
    (fr.contMDiff_comp (List.finRange k)).comp
      (contMDiff_fst.prodMk (fr.contMDiff_level_val'.comp contMDiff_snd))

end Frame

end CutCur
