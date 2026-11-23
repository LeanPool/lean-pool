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

private theorem chart_prod_transport {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
    [MeasurableSpace B] [BorelSpace B] [MeasurableSpace C] [BorelSpace C]
    (e : OpenPartialHomeomorph B C) {μ : Measure (A × B)}
    {γ : Measure A} [SFinite γ] {ν : Measure B} [SFinite ν]
    (h : (μ.restrict (univ ×ˢ e.source)).map (Prod.map id e) =
      γ.prod ((ν.restrict e.source).map e)) :
    μ.restrict (univ ×ˢ e.source) = γ.prod (ν.restrict e.source) := by
  let p := (OpenPartialHomeomorph.refl A).prod e
  have source_eq : p.source = univ ×ˢ e.source := rfl
  have map_eq : ⇑p = Prod.map id e := rfl
  have product_restrict : (γ.prod ν).restrict (univ ×ˢ e.source) =
      γ.prod (ν.restrict e.source) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [← product_restrict]
  apply chart_map_restrict_injective p
  rw [source_eq, map_eq, h, product_restrict, ← Measure.map_prod_map_of_aemeasurable γ _
    measurable_id.aemeasurable (e.continuousOn.aemeasurable e.open_source.measurableSet),
    Measure.map_id]

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
  let ψ := chartAt (LevelModel F (Rd k)) y₀
  have marginal_restrict : ((μ.map fr.toLevel).restrict ψ.source) =
      (μ.restrict (fr.Θ y₀).source).map fr.toLevel := by
    rw [Measure.restrict_map fr.measurable_toLevel ψ.open_source.measurableSet, fr.Θ_source]
    rfl
  have chart_measurable : AEMeasurable ψ ((μ.map fr.toLevel).restrict ψ.source) :=
    ψ.continuousOn.aemeasurable ψ.open_source.measurableSet
  have product_chart_measurable : AEMeasurable (fr.Θ y₀) (μ.restrict (fr.Θ y₀).source) :=
    (fr.Θ y₀).continuousOn.aemeasurable (fr.Θ y₀).open_source.measurableSet
  change (((μ.map fr.toLevel).restrict ψ.source).map ψ) = _
  rw [marginal_restrict] at chart_measurable ⊢
  rw [chart_measurable.map_map_of_aemeasurable fr.measurable_toLevel.aemeasurable,
    show ψ ∘ fr.toLevel = Prod.snd ∘ fr.Θ y₀ from rfl,
    ← measurable_snd.aemeasurable.map_map_of_aemeasurable product_chart_measurable,
    fr.map_Θ_prod J y₀ hV hμ hρ hVX, Measure.map_snd_prod, measure_univ, one_smul]
  rfl

include J hV hμ hρ hVX in
/-- Local form of the factorization: over the chart domain of `y₀`. -/
theorem restrict_splitEquiv :
    (μ.map fr.splitEquiv).restrict (univ ×ˢ (chartAt (LevelModel F (Rd k))
        y₀).source) =
      (multivariateGaussian (0 : Rd k)
        (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).prod
        ((μ.map fr.toLevel).restrict
          (chartAt (LevelModel F (Rd k)) y₀).source) := by
  let ψ := chartAt (LevelModel F (Rd k)) y₀
  have source_measurable : MeasurableSet (univ ×ˢ ψ.source : Set (Rd k × fr.Level)) :=
    MeasurableSet.univ.prod ψ.open_source.measurableSet
  have split_measurable : Measurable fr.splitEquiv := fr.splitEquiv.continuous.measurable
  have preimage_eq : fr.splitEquiv ⁻¹' (univ ×ˢ ψ.source) = (fr.Θ y₀).source := by
    rw [fr.Θ_source]
    ext x
    simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_ofPred_eq]
    rfl
  apply chart_prod_transport ψ
  have chart_measurable : AEMeasurable (Prod.map id ψ)
      ((μ.map fr.splitEquiv).restrict (univ ×ˢ ψ.source)) :=
    (continuous_id.continuousOn.prodMap ψ.continuousOn).aemeasurable source_measurable
  rw [Measure.restrict_map split_measurable source_measurable, preimage_eq] at chart_measurable ⊢
  rw [chart_measurable.map_map_of_aemeasurable split_measurable.aemeasurable]
  rw [fr.map_level_chart J hV hμ hρ hVX y₀]
  exact fr.map_Θ_prod J y₀ hV hμ hρ hVX

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
