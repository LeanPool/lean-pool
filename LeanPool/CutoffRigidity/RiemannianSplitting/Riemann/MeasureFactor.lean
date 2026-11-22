/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.MeasureProduct

/-! # Density of the weighted volume in the product charts -/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

namespace Frame

open CutoffRigidity CutoffRigidity.Riemann

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] {k : ℕ} (fr : Frame F M k)
  [MeasurableSpace M] [BorelSpace M]

variable (J : WithLp 2 (Rd k ×
    LevelModel F (Rd k)) ≃ₗᵢ[ℝ] F) (y₀ : fr.Level)

/-- `Jc J` as a measurable equivalence. -/
noncomputable def eJ : (Rd k × LevelModel F (Rd k)) ≃ᵐ F :=
  (MeasurableEquiv.toLp 2 (Rd k × LevelModel F (EuclideanSpace ℝ (Fin
      k)))).trans
    J.toHomeomorph.toMeasurableEquiv

omit [FiniteDimensional ℝ F] in
theorem eJ_apply (p : Rd k × LevelModel F (Rd k)) :
    eJ J p = Jc J p := rfl

theorem measurePreserving_eJ : MeasurePreserving (eJ J) volume volume :=
  J.measurePreserving.comp (WithLp.volume_preserving_toLp _ _)

omit [MeasurableSpace M] [BorelSpace M] in
theorem eJ_mem_target_iff (p : Rd k × LevelModel F (Rd k)) :
    eJ J p ∈ (fr.Ξ J y₀).target ↔ p ∈ (fr.prodChart y₀).target := by
  rw [eJ_apply, fr.Ξ_target' J y₀]
  simp

omit [MeasurableSpace M] [BorelSpace M] in
theorem Ξ_symm_eJ (p : Rd k × LevelModel F (Rd k)) :
    (fr.Ξ J y₀).symm (eJ J p) = (fr.Θ y₀).symm p := by
  rw [eJ_apply]
  simp [Ξ]

include J in
/-- The weighted volume in the product chart (before the potential is split). -/
theorem map_Θ_eq [SecondCountableTopology M] {V : M → ℝ} {μ : Measure M}
    (hμ : IsWeightedVolume F μ V) :
    (μ.restrict (fr.Θ y₀).source).map (fr.Θ y₀) =
      ((volume : Measure (Rd k ×
        LevelModel F (Rd k))).restrict (fr.prodChart y₀).target).withDensity
        (fun p => ENNReal.ofReal (Real.exp (-V ((fr.Θ y₀).symm p)) *
          chartVolumeDensity (LevelModel F (Rd k)) y₀ p.2)) := by
  set S := (fr.Θ y₀).source with hS
  have hΞS : (fr.Ξ J y₀).source = S := fr.Ξ_source J y₀
  have hmain := map_chart_density hμ (fr.Ξ J y₀) ((fr.contMDiffOn_Ξ J y₀).of_le (by simp))
    ((fr.contMDiffOn_Ξ_symm J y₀).of_le (by simp))
  rw [hΞS] at hmain
  have hSm : MeasurableSet S := (fr.Θ y₀).open_source.measurableSet
  have hΞm : AEMeasurable (fr.Ξ J y₀) (μ.restrict S) := by
    have := (fr.Ξ J y₀).continuousOn.aemeasurable (μ := μ) (fr.Ξ J y₀).open_source.measurableSet
    rwa [hΞS] at this
  have hae : (fr.Θ y₀) =ᵐ[μ.restrict S] (eJ J).symm ∘ (fr.Ξ J y₀) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hSm]
    refine Filter.Eventually.of_forall fun x hx => ?_
    simp [Ξ, eJ, Jc]
  rw [Measure.map_congr hae, ← AEMeasurable.map_map_of_aemeasurable (eJ
      J).symm.measurable.aemeasurable
    hΞm, hmain]
  ext B hB
  rw [Measure.map_apply (eJ J).symm.measurable hB, withDensity_apply _ ((eJ J).symm.measurable hB),
    withDensity_apply _ hB, Measure.restrict_restrict ((eJ J).symm.measurable hB),
    Measure.restrict_restrict hB]
  have hpre : eJ J ⁻¹' ((eJ J).symm ⁻¹' B ∩ (fr.Ξ J y₀).target) =
      B ∩ (fr.prodChart y₀).target := by
    ext p
    simp only [mem_preimage, mem_inter_iff, MeasurableEquiv.symm_apply_apply]
    rw [fr.eJ_mem_target_iff J y₀]
  rw [← (measurePreserving_eJ J).setLIntegral_comp_preimage_emb (eJ J).measurableEmbedding _
    ((eJ J).symm ⁻¹' B ∩ (fr.Ξ J y₀).target), hpre]
  refine setLIntegral_congr_fun (hB.inter (fr.prodChart y₀).open_target.measurableSet) fun p hp =>
      ?_
  have hp' : eJ J p ∈ (fr.Ξ J y₀).target := (fr.eJ_mem_target_iff J y₀ p).2 hp.2
  rw [Ξ_symm_eJ, eJ_apply, chartDensity_Ξ fr J y₀ _ (by rwa [← eJ_apply])]
  have : zc J ((Jc J) p) = p.2 := by simp [zc]
  rw [this]

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M] in
theorem Θ_symm_apply (p : Rd k × LevelModel F (Rd k)) :
    (fr.Θ y₀).symm p = fr.comp (List.finRange k) p.1
      ((chartAt (LevelModel F (Rd k)) y₀).symm p.2).val := by
  simp [Θ, prodChart, splitEquiv]
  rfl

/-- The potential of the level factor. -/
noncomputable def Vlev (V : M → ℝ) (ρ : ℝ) (y : fr.Level) : ℝ :=
  V y.val + (k / 2 : ℝ) * Real.log (ρ / (2 * Real.pi))

include J in
/-- The weighted volume in the product chart splits as Gaussian times the level density. -/
theorem map_Θ_prod [SecondCountableTopology M] {V : M → ℝ}
    (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V) {μ : Measure M} (hμ : IsWeightedVolume F μ V)
    {ρ : ℝ} (hρ : 0 < ρ) (hVX : ∀ i x, mvfderiv 𝓘(ℝ, F) V x (fr.X i x) = ρ * fr.s i x) :
    (μ.restrict (fr.Θ y₀).source).map (fr.Θ y₀) =
      (ProbabilityTheory.multivariateGaussian (0 : Rd k)
        (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).prod
      (((volume : Measure (LevelModel F (Rd k))).restrict
          (chartAt (LevelModel F (Rd k)) y₀).target).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-fr.Vlev V ρ
          ((chartAt (LevelModel F (Rd k)) y₀).symm z)) *
          chartVolumeDensity (LevelModel F (Rd k)) y₀ z))) := by
  set ψ := chartAt (LevelModel F (Rd k)) y₀ with hψ
  have hg : AEMeasurable (fun z : LevelModel F (Rd k) =>
      ENNReal.ofReal (Real.exp (-fr.Vlev V ρ (ψ.symm z)) *
        chartVolumeDensity (LevelModel F (Rd k)) y₀ z))
      ((volume : Measure (LevelModel F (Rd k))).restrict ψ.target) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    refine ContinuousOn.aemeasurable ?_ ψ.open_target.measurableSet
    refine ContinuousOn.mul ?_ (continuousOn_chartVolumeDensity _ y₀)
    refine Real.continuous_exp.comp_continuousOn (ContinuousOn.neg ?_)
    have hVl : Continuous (fr.Vlev V ρ) := by
      unfold Vlev
      exact (hV.continuous.comp fr.contMDiff_level_val'.continuous).add continuous_const
    exact hVl.comp_continuousOn ψ.continuousOn_symm
  rw [fr.map_Θ_eq J y₀ hμ, multivariateGaussian_eq_withDensity k hρ,
    prod_withDensity₀ (by fun_prop) hg]
  have hprod : (volume : Measure (Rd k ×
      LevelModel F (Rd k))).restrict (fr.prodChart y₀).target =
      (volume : Measure (Rd k)).prod
        ((volume : Measure (LevelModel F (Rd k))).restrict ψ.target) := by
    have := Measure.prod_restrict (μ := (volume : Measure (Rd k)))
      (ν := (volume : Measure (LevelModel F (Rd k)))) univ ψ.target
    rw [Measure.restrict_univ] at this
    rw [this, prodChart_target]
    rfl
  rw [← hprod]
  refine withDensity_congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' (fr.prodChart y₀).open_target.measurableSet]
  refine Filter.Eventually.of_forall fun p hp => ?_
  rw [prodChart_target] at hp
  have hpt := hp.2
  change ENNReal.ofReal (Real.exp (-V ((fr.Θ y₀).symm p)) *
      chartVolumeDensity (LevelModel F (Rd k)) y₀ p.2) = _
  rw [fr.Θ_symm_apply y₀ p, fr.V_action hV hVX p.1 _ ((ψ.symm p.2).property)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hc : (ρ / (2 * Real.pi)) ^ ((k : ℝ) / 2) =
      Real.exp (Real.log (ρ / (2 * Real.pi)) * ((k : ℝ) / 2)) :=
    Real.rpow_def_of_pos (by positivity) _
  rw [hc]
  unfold Vlev
  set D := chartVolumeDensity (LevelModel F (Rd k)) y₀ p.2
  set L := Real.log (ρ / (2 * Real.pi))
  have : -(V ↑(ψ.symm p.2) + ρ * ‖p.1‖ ^ 2 / 2) = L * (k / 2) + -(ρ / 2) * ‖p.1‖ ^ 2 +
      -(V ↑(ψ.symm p.2) + (k / 2) * L) := by ring
  rw [this, Real.exp_add, Real.exp_add]
  ring

end Frame

end CutCur
