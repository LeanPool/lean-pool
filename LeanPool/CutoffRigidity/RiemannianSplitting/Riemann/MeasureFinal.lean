/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.MeasureFactor
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedSigmaCompact

/-! # The measure factorization for the splitting -/

@[expose] public section

open Bundle MeasureTheory Set ProbabilityTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

namespace Frame

open CutoffRigidity CutoffRigidity.Riemann

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] {k : ℕ} (fr : Frame F M k)

include fr in
omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem k_le_finrank (x : M) : k ≤ Module.finrank ℝ F := by
  have hs := fr.surjective_mfderiv_sv x
  have h1 := LinearMap.finrank_range_le
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, Rd k) fr.sv x).toLinearMap
  rw [LinearMap.range_eq_top.mpr hs] at h1
  have h2 : Module.finrank ℝ (TangentSpace (𝓡 k) (fr.sv x)) = k := by
    change Module.finrank ℝ (Rd k) = k
    simp
  have h3 : Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x) = Module.finrank ℝ F := rfl
  rw [finrank_top] at h1
  change Module.finrank ℝ (TangentSpace (𝓡 k) (fr.sv x)) ≤
    Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x) at h1
  rwa [h2, h3] at h1

include fr in
omit [IsRiemannianManifold 𝓘(ℝ, F) M] [CompleteSpace M] in
theorem exists_J (x : M) : Nonempty (WithLp 2 (Rd k ×
    LevelModel F (Rd k)) ≃ₗᵢ[ℝ] F) := by
  have hk := fr.k_le_finrank x
  have hfr : Module.finrank ℝ (WithLp 2 (Rd k ×
      LevelModel F (Rd k))) = Module.finrank ℝ F := by
    rw [(WithLp.linearEquiv 2 ℝ (Rd k ×
      LevelModel F (Rd k))).finrank_eq, Module.finrank_prod]
    simp
    omega
  exact ⟨(stdOrthonormalBasis ℝ _).repr.trans ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finCongr hfr)).trans (stdOrthonormalBasis ℝ F).repr.symm)⟩

section Measure

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

omit [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology M] in
theorem measurable_toLevel : Measurable fr.toLevel :=
  fr.contMDiff_toLevel.continuous.measurable

/-- The density measure of the level chart at `y₀`. -/
noncomputable def levelMeasure (V : M → ℝ) (ρ : ℝ) (y₀ : fr.Level) :
    Measure (LevelModel F (Rd k)) :=
  ((volume : Measure (LevelModel F (Rd k))).restrict
    (chartAt (LevelModel F (Rd k)) y₀).target).withDensity
  (fun z => ENNReal.ofReal (Real.exp (-fr.Vlev V ρ
    ((chartAt (LevelModel F (Rd k)) y₀).symm z)) *
    chartVolumeDensity (LevelModel F (Rd k)) y₀ z))

variable (J : WithLp 2 (Rd k ×
    LevelModel F (Rd k)) ≃ₗᵢ[ℝ] F) {V : M → ℝ}
  (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V) {μ : Measure M} [IsProbabilityMeasure μ] (hμ :
      IsWeightedVolume F μ V)
  {ρ : ℝ} (hρ : 0 < ρ) (hVX : ∀ i x, mvfderiv 𝓘(ℝ, F) V x (fr.X i x) = ρ * fr.s i x)
  (y₀ : fr.Level)

omit [MeasurableSpace F]
  [BorelSpace F]
  [MeasurableSpace M]
  [BorelSpace M]
  [SecondCountableTopology M] in
theorem Θ_apply (x : M) : (fr.Θ y₀) x = (fr.sv x,
    (chartAt (LevelModel F (Rd k)) y₀) (fr.toLevel x)) := rfl

include J hV hμ hρ hVX in
omit [IsProbabilityMeasure μ] in
/-- The level density measure is the chart image of the level marginal. -/
theorem map_level_chart :
    ((μ.map fr.toLevel).restrict (chartAt (LevelModel F (Rd k)) y₀).source).map
      (chartAt (LevelModel F (Rd k)) y₀) = fr.levelMeasure V ρ y₀ := by
  set ψ := chartAt (LevelModel F (Rd k)) y₀ with hψ
  have hΘ := fr.map_Θ_prod J y₀ hV hμ hρ hVX
  have hW : MeasurableSet ψ.source := ψ.open_source.measurableSet
  have hS : MeasurableSet (fr.Θ y₀).source := (fr.Θ y₀).open_source.measurableSet
  have hψm : AEMeasurable ψ ((μ.map fr.toLevel).restrict ψ.source) :=
    ψ.continuousOn.aemeasurable hW
  have hΘm : AEMeasurable (fr.Θ y₀) (μ.restrict (fr.Θ y₀).source) :=
    (fr.Θ y₀).continuousOn.aemeasurable hS
  ext B hB
  rw [Measure.map_apply_of_aemeasurable hψm hB, Measure.restrict_apply' hW,
    Measure.map_apply fr.measurable_toLevel
      (by simpa [inter_comm] using
        measurableSet_inter_preimage_of_continuousOn hW ψ.continuousOn hB)]
  have h1 : (fr.levelMeasure V ρ y₀) B =
      ((μ.restrict (fr.Θ y₀).source).map (fr.Θ y₀)) (univ ×ˢ B) := by
    rw [hΘ, Measure.prod_prod, measure_univ, one_mul]
    rfl
  rw [h1, Measure.map_apply_of_aemeasurable hΘm (MeasurableSet.univ.prod hB),
    Measure.restrict_apply' hS]
  congr 1
  ext x
  simp only [preimage_inter, mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and,
    Θ_source, Θ_apply]
  exact Iff.rfl

include J hV hμ hρ hVX in
/-- Local form of the factorization: over the chart domain of `y₀`. -/
theorem restrict_splitEquiv :
    (μ.map fr.splitEquiv).restrict (univ ×ˢ (chartAt (LevelModel F (Rd k))
        y₀).source) =
      (multivariateGaussian (0 : Rd k)
        (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).prod
        ((μ.map fr.toLevel).restrict
          (chartAt (LevelModel F (Rd k)) y₀).source) := by
  set ψ := chartAt (LevelModel F (Rd k)) y₀ with hψ
  have hΘ := fr.map_Θ_prod J y₀ hV hμ hρ hVX
  have hC1 := fr.map_level_chart J hV hμ hρ hVX y₀
  unfold levelMeasure at hC1
  have hW : MeasurableSet ψ.source := ψ.open_source.measurableSet
  have hS : MeasurableSet (fr.Θ y₀).source := (fr.Θ y₀).open_source.measurableSet
  have hΘm : AEMeasurable (fr.Θ y₀) (μ.restrict (fr.Θ y₀).source) :=
    (fr.Θ y₀).continuousOn.aemeasurable hS
  have hΦm : Measurable fr.splitEquiv := fr.splitEquiv.continuous.measurable
  have hrect : ∀ (s : Set (Rd k)) (t : Set fr.Level),
      MeasurableSet s → MeasurableSet t → t ⊆ ψ.source →
      μ (fr.splitEquiv ⁻¹' (s ×ˢ t)) = multivariateGaussian (0 : Rd k)
        (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) s * ((μ.map fr.toLevel).restrict ψ.source) t := by
    intro s t hs ht hts
    have hψt : MeasurableSet (⇑ψ '' t) := by
      rw [ψ.image_eq_target_inter_inv_preimage hts]
      exact measurableSet_inter_preimage_of_continuousOn ψ.open_target.measurableSet
        ψ.continuousOn_symm ht
    have hset : fr.splitEquiv ⁻¹' (s ×ˢ t) =
        (fr.Θ y₀) ⁻¹' (s ×ˢ (⇑ψ '' t)) ∩ (fr.Θ y₀).source := by
      ext x
      simp only [mem_preimage, mem_prod, mem_inter_iff, Θ_source, mem_ofPred_eq, Θ_apply, mem_image]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, _, h2, rfl⟩, hts h2⟩
      · rintro ⟨⟨h1, y, hy, hyx⟩, h3⟩
        have : y = fr.toLevel x := ψ.injOn (hts hy) h3 hyx
        subst this
        exact ⟨h1, hy⟩
    rw [hset, ← Measure.restrict_apply' hS, ← Measure.map_apply_of_aemeasurable hΘm (hs.prod hψt),
      hΘ, Measure.prod_prod, ← hC1, Measure.map_apply_of_aemeasurable
        (ψ.continuousOn.aemeasurable hW) hψt, Measure.restrict_apply' hW]
    rw [Measure.restrict_apply' hW, ψ.injOn.preimage_image_inter hts, inter_eq_left.2 hts]
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.restrict_apply (hs.prod ht), Measure.restrict_apply' hW]
  have h1 : (s ×ˢ t) ∩ (univ ×ˢ ψ.source) = s ×ˢ (t ∩ ψ.source) := by
    ext x; simp [and_assoc]
  rw [h1, Measure.map_apply hΦm (hs.prod (ht.inter hW)), hrect s (t ∩ ψ.source) hs (ht.inter hW)
    inter_subset_right, Measure.restrict_apply' hW, inter_assoc, inter_self]

end Measure

section Main

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M]

/-- **Measure factorization for the Riemannian splitting** (workstream S8).

Let `fr` be an orthonormal parallel frame with `⟨∇V, Xᵢ⟩ = ρ sᵢ` (e.g. a basis of first
eigenfunctions) and `μ = e^{-V} vol` a probability measure on the complete manifold `M`.
Then, with `V' = V∘val + (k/2) log(ρ/2π)` on the level `N = {s = 0}` and `μ' = μ.map toLevel`,
`V'` is smooth, `μ'` is a probability measure with density `e^{-V'} vol_{g_N}` in the charts of `N`
(`IsWeightedVolume`) and `μ.map Φ = γ_{k,ρ⁻¹} ⊗ μ'`, `Φ = fr.splitEquiv`. -/
theorem weighted_factorization {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hVX : ∀ i x, mvfderiv 𝓘(ℝ, F) V x (fr.X i x) = ρ * fr.s i x) :
    let V' := fr.Vlev V ρ
    let μ' : Measure fr.Level := μ.map fr.toLevel
    ContMDiff 𝓘(ℝ, LevelModel F (Rd k)) 𝓘(ℝ, ℝ) ∞ V' ∧
      IsProbabilityMeasure μ' ∧
      IsWeightedVolume (LevelModel F (Rd k)) μ' V' ∧
      μ.map fr.splitEquiv =
        (multivariateGaussian 0 (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).prod μ' := by
  intro V' μ'
  have hne : (univ : Set M).Nonempty := nonempty_of_measure_ne_zero (μ := μ) (by simp)
  obtain ⟨x₀⟩ := hne.to_subtype
  obtain ⟨J⟩ := fr.exists_J x₀
  have : SigmaCompactSpace M := sigmaCompactSpace_of_finite_weightedVolume F hV hμ
  have : SecondCountableTopology M := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hV.comp fr.contMDiff_level_val').add contMDiff_const
  · exact inferInstanceAs (IsProbabilityMeasure (μ.map fr.toLevel))
  · intro y₀
    exact fr.map_level_chart J hV hμ hρ hVX y₀
  · have hcov := TopologicalSpace.countable_cover_nhds (α := fr.Level)
      (f := fun y => (chartAt (LevelModel F (Rd k)) y).source)
      (fun y => (chartAt (LevelModel F (Rd k)) y).open_source.mem_nhds
        (mem_chart_source _ y))
    obtain ⟨t, htc, hcov⟩ := hcov
    have : Countable t := htc.to_subtype
    set γ := multivariateGaussian (0 : Rd k)
      (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) with hγ
    have hpiece : ∀ i : t, (μ.map fr.splitEquiv).restrict
        (univ ×ˢ (chartAt (LevelModel F (Rd k)) (i : fr.Level)).source) =
        (γ.prod (μ.map fr.toLevel)).restrict
        (univ ×ˢ (chartAt (LevelModel F (Rd k)) (i : fr.Level)).source) := by
      intro i
      rw [fr.restrict_splitEquiv J hV hμ hρ hVX (i : fr.Level)]
      have := Measure.prod_restrict (μ := γ) (ν := μ.map fr.toLevel) univ
        (chartAt (LevelModel F (Rd k)) (i : fr.Level)).source
      rw [Measure.restrict_univ] at this
      exact this
    have hU : ⋃ i : t, (univ ×ˢ (chartAt (LevelModel F (Rd k)) (i :
        fr.Level)).source :
        Set (Rd k × fr.Level)) = univ := by
      ext p
      simp only [mem_iUnion, mem_prod, mem_univ, true_and, iff_true]
      have hp : p.2 ∈ ⋃ x ∈ t, (chartAt (LevelModel F (Rd k)) x).source := by
        rw [hcov]; exact mem_univ _
      simp only [mem_iUnion] at hp
      obtain ⟨y, hy, hpy⟩ := hp
      exact ⟨⟨y, hy⟩, hpy⟩
    have := Measure.restrict_iUnion_congr.2 hpiece
    rw [hU, Measure.restrict_univ, Measure.restrict_univ] at this
    exact this

end Main

end Frame

end CutCur
