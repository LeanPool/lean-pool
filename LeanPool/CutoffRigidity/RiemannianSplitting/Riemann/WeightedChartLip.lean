/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedProper
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # Riemannian distance in charts, with sharp local constants
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Manifold
open scoped Manifold ContDiff ENNReal Topology


namespace CutCur

section ChartLip

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

include F

/-- The trivialization of the tangent bundle at `p`, inverse map at the point `y`. -/
noncomputable abbrev symmAt (p y : M) : F →L[ℝ] TangentSpace 𝓘(ℝ, F) y :=
  (trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p).symmL ℝ y

omit [FiniteDimensional ℝ F] in
theorem eventually_symmAt_norm (p : M) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 p, y ∈ (chartAt F p).source ∧
      (∀ w, ‖symmAt F p y w‖ ≤ r * ‖symmAt F p p w‖) ∧
      (∀ w, ‖symmAt F p p w‖ ≤ r * ‖symmAt F p y w‖) := by
  have := isContinuousRiemannianBundle_tangent (F := F) (M := M)
  filter_upwards [eventually_norm_symmL_trivializationAt_comp_self_lt F
      (fun x : M => TangentSpace 𝓘(ℝ, F) x) p hr,
    eventually_norm_symmL_trivializationAt_self_comp_lt F
      (fun x : M => TangentSpace 𝓘(ℝ, F) x) p hr, chart_source_mem_nhds F p] with y h1 h2 h3
  refine ⟨h3, fun w => ?_, fun w => ?_⟩
  · have hp : p ∈ (trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' p
    set T := trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p
    have e : T.continuousLinearMapAt ℝ p (T.symmL ℝ p w) = w :=
      Trivialization.continuousLinearMapAt_symmL _ hp w
    have key := ContinuousLinearMap.le_opNorm ((T.symmL ℝ y) ∘L (T.continuousLinearMapAt ℝ p))
      (T.symmL ℝ p w)
    rw [ContinuousLinearMap.comp_apply, e] at key
    exact key.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg _))
  · have hy : y ∈ (trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p).baseSet := by
      simpa using h3
    set T := trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p
    have e : T.continuousLinearMapAt ℝ y (T.symmL ℝ y w) = w :=
      Trivialization.continuousLinearMapAt_symmL _ hy w
    have key := ContinuousLinearMap.le_opNorm ((T.symmL ℝ p) ∘L (T.continuousLinearMapAt ℝ y))
      (T.symmL ℝ y w)
    rw [ContinuousLinearMap.comp_apply, e] at key
    exact key.trans (mul_le_mul_of_nonneg_right h2.le (norm_nonneg _))

variable [IsRiemannianManifold 𝓘(ℝ, F) M]

omit [FiniteDimensional ℝ F] in
/-- Sharp local Lipschitz bound of the inverse extended chart, for the Riemannian distance. -/
theorem edist_extChartAt_symm_le (p : M) {r R : ℝ} (_hr : 0 ≤ r)
    (hRt : Metric.ball (extChartAt 𝓘(ℝ, F) p p) R ⊆ (extChartAt 𝓘(ℝ, F) p).target)
    (hgood : ∀ ζ ∈ Metric.ball (extChartAt 𝓘(ℝ, F) p p) R, ∀ w,
      ‖symmAt F p ((extChartAt 𝓘(ℝ, F) p).symm ζ) w‖ ≤ r * ‖symmAt F p p w‖)
    {b b' : F} (hb : b ∈ Metric.ball (extChartAt 𝓘(ℝ, F) p p) R)
    (hb' : b' ∈ Metric.ball (extChartAt 𝓘(ℝ, F) p p) R) :
    edist ((extChartAt 𝓘(ℝ, F) p).symm b) ((extChartAt 𝓘(ℝ, F) p).symm b') ≤
      ENNReal.ofReal (r * ‖symmAt F p p (b' - b)‖) := by
  have := isContinuousRiemannianBundle_tangent (F := F) (M := M)
  set e := extChartAt 𝓘(ℝ, F) p with he
  let η := ContinuousAffineMap.lineMap (R := ℝ) b b'
  set γ := e.symm ∘ η with hγ
  have hη : Icc (0 : ℝ) 1 ⊆ ⇑η ⁻¹' (Metric.ball (e p) R) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    exact (convex_ball _ _).segment_subset hb hb'
  have hηt : Icc (0 : ℝ) 1 ⊆ ⇑η ⁻¹' e.target := hη.trans (preimage_mono hRt)
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hle : riemannianEDist 𝓘(ℝ, F) (e.symm b) (e.symm b') ≤ pathELength 𝓘(ℝ, F) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm p).comp η_smooth hηt
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, F))]
  refine hle.trans ?_
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  calc ∫⁻ t in Icc (0 : ℝ) 1, ‖mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ (Icc 0 1) t 1‖ₑ
      ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (r * ‖symmAt F p p (b' - b)‖) := by
        apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
        have hd : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ (Icc 0 1) t =
            (mfderivWithin 𝓘(ℝ, F) 𝓘(ℝ, F) e.symm (range 𝓘(ℝ, F)) (η t)) ∘L
              (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) η (Icc 0 1) t) := by
          apply mfderivWithin_comp
          · exact mdifferentiableWithinAt_extChartAt_symm (hηt ht)
          · exact η_smooth.mdifferentiableOn one_ne_zero t ht
          · exact hηt.trans (preimage_mono (extChartAt_target_subset_range p))
          · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact uniqueDiffOn_Icc zero_lt_one t ht
        have hd1 : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) η (Icc 0 1) t 1 = b' - b := by
          rw [mfderivWithin_eq_fderivWithin,
            fderivWithin_eq_fderiv (uniqueDiffOn_Icc zero_lt_one _ ht)
              (ContinuousAffineMap.differentiableAt _)]
          exact (by simp : b' - b = fderiv ℝ (ContinuousAffineMap.lineMap (R := ℝ) b b') t 1).symm
        have hmem : e.symm (η t) ∈ (chartAt F p).source := by
          have := e.map_target (hηt ht)
          simpa [he, extChartAt_source] using this
        have hsym : mfderivWithin 𝓘(ℝ, F) 𝓘(ℝ, F) e.symm (range 𝓘(ℝ, F)) (η t) = symmAt F p
            (e.symm (η t)) := by
          rw [symmAt, TangentBundle.symmL_trivializationAt hmem]
          congr 1
          exact (e.right_inv (hηt ht)).symm
        have h1 : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ (Icc 0 1) t 1 =
            (mfderivWithin 𝓘(ℝ, F) 𝓘(ℝ, F) e.symm (range 𝓘(ℝ, F)) (η t))
              (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) η (Icc 0 1) t 1) := congr($hd 1)
        rw [h1, hd1, hsym, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hgood _ (hη ht) _)
    _ = ENNReal.ofReal (r * ‖symmAt F p p (b' - b)‖) := by simp

end ChartLip

end CutCur
