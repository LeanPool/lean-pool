/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.MeasureChart
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.MeasureGram
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitRiemannLevel
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitWeight
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitGaussian

/-! # The Riemannian density of the level `N` computed in `M` -/

@[expose] public section

open Bundle MeasureTheory Set
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
/-- The differential of the inclusion of the level preserves inner products. -/
theorem inner_mfderiv_level_val (y : fr.Level)
    (v w : TangentSpace 𝓘(ℝ, LevelModel F (Rd k)) y) :
    inner ℝ (mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
      (Subtype.val : fr.Level → M) y v)
      (mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
      (Subtype.val : fr.Level → M) y w) = inner ℝ v w := by
  let T : TangentSpace 𝓘(ℝ, LevelModel F (Rd k)) y →ₗᵢ[ℝ]
      TangentSpace 𝓘(ℝ, F) y.val :=
    { toLinearMap := (mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
        (Subtype.val : fr.Level → M) y).toLinearMap
      norm_map' := fun v => fr.norm_mfderiv_level_val y v }
  exact T.inner_map_map v w

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem inner_X_mfderiv_level_val (i : Fin k) (y : fr.Level)
    (v : TangentSpace 𝓘(ℝ, LevelModel F (Rd k)) y) :
    inner ℝ (fr.X i y.val) (mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
      (Subtype.val : fr.Level → M) y v) = 0 := by
  rw [Frame.X, inner_mgrad]
  have hs : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fr.s i) y.val :=
    ((fr.smooth i).mdifferentiable (by simp)) _
  have hval : MDifferentiableAt 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
      (Subtype.val : fr.Level → M) y := (fr.contMDiff_level_val'.mdifferentiable (by simp)) _
  have hc : (fun z : fr.Level => fr.s i z.val) = fun _ => (0 : ℝ) := by
    funext z
    have := congrArg (fun v : EuclideanSpace ℝ (Fin k) => v i) z.property
    simpa [sv] using this
  rw [← mvfderiv_comp_apply y hs hval v]
  change mvfderiv 𝓘(ℝ, LevelModel F (Rd k)) (fun z : fr.Level ↦ fr.s i z.val) y v = 0
  rw [hc, mvfderiv_const, zero_apply]

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
/-- Chain rule for the inclusion of the level composed with a chart inverse. -/
theorem mfderiv_val_chart_symm (y₀ : fr.Level) {z : LevelModel F (Rd k)}
    (hz : z ∈ (chartAt (LevelModel F (Rd k)) y₀).target)
    (v : LevelModel F (Rd k)) :
    mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
      (fun z => ((chartAt (LevelModel F (Rd k)) y₀).symm z).val) z v =
    mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
      (Subtype.val : fr.Level → M) ((chartAt (LevelModel F (Rd k)) y₀).symm z)
      (mfderiv 𝓘(ℝ, LevelModel F (Rd k))
        𝓘(ℝ, LevelModel F (Rd k))
        (chartAt (LevelModel F (Rd k)) y₀).symm z v) := by
  set ψ := chartAt (LevelModel F (Rd k)) y₀ with hψ
  have hψd : MDifferentiableAt 𝓘(ℝ, LevelModel F (Rd k))
      𝓘(ℝ, LevelModel F (Rd k)) ψ.symm z :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℝ, LevelModel F (Rd k))) (n := ∞)
      (x := y₀)).mdifferentiableOn (by simp) z hz).mdifferentiableAt (ψ.open_target.mem_nhds hz)
  have hval : MDifferentiableAt 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
      (Subtype.val : fr.Level → M) (ψ.symm z) :=
    (fr.contMDiff_level_val'.mdifferentiable (by simp)) _
  have h1 := mfderiv_comp z hval hψd
  change mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
      ((Subtype.val : fr.Level → M) ∘ ψ.symm) z v = _
  rw [h1]; rfl

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
/-- The Riemannian density of the level, computed with the inclusion into `M`. -/
theorem chartVolumeDensity_level (y₀ : fr.Level) {z : LevelModel F (Rd k)}
    (hz : z ∈ (chartAt (LevelModel F (Rd k)) y₀).target) :
    chartVolumeDensity (LevelModel F (Rd k)) y₀ z =
      gramDens (show LevelModel F (Rd k) →ₗ[ℝ]
          TangentSpace 𝓘(ℝ, F) ((chartAt (LevelModel F (Rd k)) y₀).symm z).val
              from
        (mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
          (fun z => ((chartAt (LevelModel F (Rd k)) y₀).symm z).val)
              z).toLinearMap) := by
  set ψ := chartAt (LevelModel F (Rd k)) y₀ with hψ
  rw [chartVolumeDensity_eq_chartDensity]
  unfold chartDensity gramDens
  congr 2
  funext i j
  have key := fr.mfderiv_val_chart_symm y₀ hz
  change inner ℝ (mfderiv 𝓘(ℝ, LevelModel F (Rd k))
          𝓘(ℝ, LevelModel F (Rd k)) ψ.symm z _)
        (mfderiv 𝓘(ℝ, LevelModel F (Rd k))
          𝓘(ℝ, LevelModel F (Rd k)) ψ.symm z _) =
      inner ℝ (mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
        (fun z => (ψ.symm z).val) z _)
        (mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
        (fun z => (ψ.symm z).val) z _)
  refine Eq.symm ?_
  refine (congrArg₂ (fun a b => inner ℝ a b) (key _) (key _)).trans ?_
  exact fr.inner_mfderiv_level_val _ _ _

end Frame

end CutCur
