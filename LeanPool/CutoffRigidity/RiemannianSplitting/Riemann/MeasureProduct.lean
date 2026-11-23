/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.MeasureLevel
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitProduct

/-! # Product charts of `M ≃ ℝ^k × N`, as charts of `M` with values in `F`

For `J : ℝ^k ⊕₂ F' ≃ₗᵢ F` and `y₀ ∈ N`, `Ξ J y₀ := J ∘ (id × chartAt y₀) ∘ Φ` is a smooth chart of
    `M`
with values in `F`; its Riemannian density is the density of the chart of `N` at `y₀`.
-/

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

/-- The continuous linear equivalence `ℝ^k × F' ≃ F` attached to an isometry for the `L²` product.
-/
noncomputable def Jc (J : WithLp 2 (Rd k ×
    LevelModel F (Rd k)) ≃ₗᵢ[ℝ] F) :
    (Rd k × LevelModel F (Rd k)) ≃L[ℝ] F :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Rd k)
    (LevelModel F (Rd k))).symm.trans J.toContinuousLinearEquiv

/-- The product chart of `ℝ^k × N` at `(·, y₀)`. -/
noncomputable def prodChart (y₀ : fr.Level) :
    OpenPartialHomeomorph (Rd k × fr.Level)
      (Rd k × LevelModel F (Rd k)) :=
  (OpenPartialHomeomorph.refl (Rd k)).prod
    (chartAt (LevelModel F (Rd k)) y₀)

/-- The product chart, pulled back to `M` by the splitting. -/
noncomputable def Θ (y₀ : fr.Level) : OpenPartialHomeomorph M
    (Rd k × LevelModel F (Rd k)) :=
  fr.splitEquiv.toHomeomorph.toOpenPartialHomeomorph.trans (fr.prodChart y₀)

/-- The product chart as a chart of `M` with values in `F`. -/
noncomputable def Ξ (J : WithLp 2 (Rd k ×
    LevelModel F (Rd k)) ≃ₗᵢ[ℝ] F) (y₀ : fr.Level) :
    OpenPartialHomeomorph M F :=
  (fr.Θ y₀).trans (Jc J).toHomeomorph.toOpenPartialHomeomorph

variable (J : WithLp 2 (Rd k ×
    LevelModel F (Rd k)) ≃ₗᵢ[ℝ] F) (y₀ : fr.Level)

theorem Θ_source : (fr.Θ y₀).source = {x | fr.toLevel x ∈ (chartAt (LevelModel F (EuclideanSpace ℝ
    (Fin k))) y₀).source} := by
  ext x
  simp [Θ, prodChart, toLevel, splitEquiv]
  rfl

theorem Ξ_target : (fr.Ξ J y₀).target = (Jc J).symm ⁻¹'
    (univ ×ˢ (chartAt (LevelModel F (Rd k)) y₀).target) := by
  ext w
  simp [Ξ, Θ, prodChart]

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem prodChart_target : (fr.prodChart y₀).target =
    univ ×ˢ (chartAt (LevelModel F (Rd k)) y₀).target := by
  simp [prodChart]

theorem Ξ_target' (w : F) : w ∈ (fr.Ξ J y₀).target ↔ (Jc J).symm w ∈ (fr.prodChart y₀).target := by
  rw [Ξ_target, prodChart_target]; rfl

theorem Ξ_source : (fr.Ξ J y₀).source = (fr.Θ y₀).source := by
  ext x
  simp [Ξ]

omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem contMDiffOn_prodChart_symm : ContMDiffOn
    𝓘(ℝ, Rd k × LevelModel F (Rd k))
    (𝓘(ℝ, Rd k).prod 𝓘(ℝ, LevelModel F (Rd k))) ∞
    (fr.prodChart y₀).symm (fr.prodChart y₀).target :=
  contMDiffOn_chart_symm (I := 𝓘(ℝ, Rd k).prod
    𝓘(ℝ, LevelModel F (Rd k))) (n := ∞) (x := ((0 : Rd k), y₀))

theorem contMDiffOn_Ξ_symm :
    ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (fr.Ξ J y₀).symm (fr.Ξ J y₀).target := by
  have h1 := fr.contMDiffOn_prodChart_symm y₀
  have h2 : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, Rd k × LevelModel F (EuclideanSpace ℝ (Fin
      k)))
      ∞ (Jc J).symm := (Jc J).symm.contDiff.contMDiff
  have h3 := fr.splitEquiv.contMDiff_invFun.comp_contMDiffOn
    (h1.comp (h2.contMDiffOn (s := (fr.Ξ J y₀).target)) (fun w hw => (fr.Ξ_target' J y₀ w).1 hw))
  refine h3.congr_mono (fun y _ => rfl) ?_
  intro w hw
  exact hw

/-- Time coordinate of a point of `F` in the product chart. -/
noncomputable abbrev tc (w : F) : Rd k := ((Jc J).symm w).1

/-- Level coordinate (in the chart of `N`) of a point of `F` in the product chart. -/
noncomputable abbrev zc (w : F) : LevelModel F (Rd k) := ((Jc J).symm w).2

/-- The point of the level corresponding to `w`. -/
noncomputable abbrev yp (w : F) : fr.Level := (chartAt (LevelModel F (Rd k))
    y₀).symm (zc J w)

/-- The differential of the inclusion of the level in the chart. -/
noncomputable abbrev uu (w : F) : LevelModel F (Rd k) →L[ℝ]
    TangentSpace 𝓘(ℝ, F) (fr.yp J y₀ w).val :=
  mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
    (fun z => ((chartAt (LevelModel F (Rd k)) y₀).symm z).val) (zc J w)

theorem mfderiv_Ξ_symm_apply (w : F) (hw : w ∈ (fr.Ξ J y₀).target) (b : F) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fr.Ξ J y₀).symm w b =
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun z' => fr.comp (List.finRange k) (tc J w) z')
        (fr.yp J y₀ w).val
        ((∑ i, (tc J b) i • fr.X i (fr.yp J y₀ w).val) + fr.uu J y₀ w (zc J b)) := by
  have hz : zc J w ∈ (chartAt (LevelModel F (Rd k)) y₀).target := by
    have := (fr.Ξ_target' J y₀ w).1 hw
    rw [prodChart_target] at this
    exact this.2
  have hf1 : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, Rd k) (fun w' => tc J w') w :=
    (((ContinuousLinearMap.fst ℝ (Rd k)
      (LevelModel F (Rd k)) ∘L
        (Jc J).symm.toContinuousLinearMap).contDiff (n := 1)).contMDiff.mdifferentiable
            one_ne_zero) w
  have hf2 : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, LevelModel F (Rd k))
      (fun w' => zc J w') w :=
    (((ContinuousLinearMap.snd ℝ (Rd k)
      (LevelModel F (Rd k)) ∘L
        (Jc J).symm.toContinuousLinearMap).contDiff (n := 1)).contMDiff.mdifferentiable
            one_ne_zero) w
  have hψd : MDifferentiableAt 𝓘(ℝ, LevelModel F (Rd k))
      𝓘(ℝ, LevelModel F (Rd k))
      (chartAt (LevelModel F (Rd k)) y₀).symm (zc J w) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℝ, LevelModel F (Rd k))) (n := ∞)
      (x := y₀)).mdifferentiableOn (by simp) _ hz).mdifferentiableAt
      ((chartAt (LevelModel F (Rd k)) y₀).open_target.mem_nhds hz)
  have hg : MDifferentiableAt 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
      (fun z => ((chartAt (LevelModel F (Rd k)) y₀).symm z).val) (zc J w) :=
    ((fr.contMDiff_level_val'.mdifferentiable (by simp)) _).comp (zc J w) hψd
  have hgf : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) (fun w' => (fr.yp J y₀ w').val) w :=
    hg.comp w hf2
  have hΛ : MDifferentiableAt 𝓘(ℝ, F)
      (𝓘(ℝ, Rd k).prod 𝓘(ℝ, F))
      (fun w' => (tc J w', (fr.yp J y₀ w').val)) w := hf1.prodMk hgf
  have hG : MDifferentiableAt (𝓘(ℝ, Rd k).prod 𝓘(ℝ, F)) 𝓘(ℝ, F)
      (fun p : Rd k × M => fr.comp (List.finRange k) p.1 p.2)
      (tc J w, (fr.yp J y₀ w).val) :=
    ((fr.contMDiff_comp (List.finRange k)).mdifferentiable (by simp)) _
  have h1 := mfderiv_comp w hG hΛ
  have h2 := mfderiv_prodMk hf1 hgf
  have h3 := mfderiv_comp w hg hf2
  have e1 : ∀ v : F, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, Rd k) (fun w' => tc J w') w v =
      tc J v := fun v => by
    rw [mfderiv_eq_fderiv]
    exact congrArg (fun L => L v) (ContinuousLinearMap.fderiv (ContinuousLinearMap.fst ℝ
      (Rd k) (LevelModel F (Rd k)) ∘L
        (Jc J).symm.toContinuousLinearMap))
  have e2 : ∀ v : F, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, LevelModel F (Rd k))
      (fun w' => zc J w') w v = zc J v := fun v => by
    rw [mfderiv_eq_fderiv]
    exact congrArg (fun L => L v) (ContinuousLinearMap.fderiv (ContinuousLinearMap.snd ℝ
      (Rd k) (LevelModel F (Rd k)) ∘L
        (Jc J).symm.toContinuousLinearMap))
  have h4 : (fr.Ξ J y₀).symm = (fun p : Rd k × M =>
      fr.comp (List.finRange k) p.1 p.2) ∘ (fun w' => (tc J w', (fr.yp J y₀ w').val)) := rfl
  rw [h4, h1]
  rw [h2]
  have e3 : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun w' => (fr.yp J y₀ w').val) w b =
      fr.uu J y₀ w (zc J b) := by
    have h5 : (fun w' => (fr.yp J y₀ w').val) = (fun z => ((chartAt (LevelModel F
        (Rd k)) y₀).symm z).val) ∘ (fun w' => zc J w') := rfl
    rw [h5, h3]
    change mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
      (fun z ↦ ((chartAt (LevelModel F (Rd k)) y₀).symm z).val) (zc J w)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, LevelModel F (Rd k)) (zc J) w b) = _
    rw [e2]
    rfl
  change mfderiv (𝓘(ℝ, Rd k).prod 𝓘(ℝ, F)) 𝓘(ℝ, F)
    (fun p : Rd k × M => fr.comp (List.finRange k) p.1 p.2)
      (tc J w, (fr.yp J y₀ w).val)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, Rd k) (fun w' => tc J w') w b,
        mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fun w' => (fr.yp J y₀ w').val) w b) = _
  rw [e1, e3, fr.mfderiv_comp_joint, map_add, map_sum]
  congr 1
  rw [Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  rw [map_smul, fr.mfderiv_comp_X (List.finRange k) (tc J w) i]

/-- **The Riemannian density of the product chart is the density of the chart of the level.** -/
theorem chartDensity_Ξ (w : F) (hw : w ∈ (fr.Ξ J y₀).target) :
    chartDensity (fr.Ξ J y₀) w =
      chartVolumeDensity (LevelModel F (Rd k)) y₀ (zc J w) := by
  have hz : zc J w ∈ (chartAt (LevelModel F (Rd k)) y₀).target := by
    have := (fr.Ξ_target' J y₀ w).1 hw
    rw [prodChart_target] at this
    exact this.2
  rw [fr.chartVolumeDensity_level y₀ hz]
  unfold chartDensity
  set m := (fr.yp J y₀ w).val with hm
  have hX : ∀ i j, inner ℝ (fr.X i m) (fr.X j m) = if i = j then (1 : ℝ) else 0 :=
    fun i j => fr.inner_X i j m
  have hu : ∀ i c, inner ℝ (fr.X i m) ((show LevelModel F (Rd k) →ₗ[ℝ]
      TangentSpace 𝓘(ℝ, F) m from (fr.uu J y₀ w).toLinearMap) c) = 0 := by
    intro i c
    have e : (fr.uu J y₀ w) c = mfderiv 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, F)
        (Subtype.val : fr.Level → M) (fr.yp J y₀ w)
        (mfderiv 𝓘(ℝ, LevelModel F (Rd k))
          𝓘(ℝ, LevelModel F (Rd k))
          (chartAt (LevelModel F (Rd k)) y₀).symm (zc J w) c) :=
      fr.mfderiv_val_chart_symm y₀ hz c
    change inner ℝ (fr.X i m) ((fr.uu J y₀ w) c) = 0
    rw [e]
    exact fr.inner_X_mfderiv_level_val i _ _
  have h2 := gramDens_sumMap (fun i => fr.X i m) hX
    (show LevelModel F (Rd k) →ₗ[ℝ] TangentSpace 𝓘(ℝ, F) m from
      (fr.uu J y₀ w).toLinearMap) hu J
  rw [← h2]
  unfold gramDens
  congr 2
  funext i j
  have key : ∀ b b' : F, inner ℝ (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fr.Ξ J y₀).symm w b)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (fr.Ξ J y₀).symm w b') =
      inner ℝ ((∑ i, (tc J b) i • fr.X i m) + fr.uu J y₀ w (zc J b))
        ((∑ i, (tc J b') i • fr.X i m) + fr.uu J y₀ w (zc J b')) := by
    intro b b'
    rw [fr.mfderiv_Ξ_symm_apply J y₀ w hw b, fr.mfderiv_Ξ_symm_apply J y₀ w hw b']
    exact fr.inner_mfderiv_comp (List.finRange k) (tc J w) m _ _
  simp only [LinearMap.comp_apply, sumMap_apply]
  exact key _ _

end Frame

end CutCur
