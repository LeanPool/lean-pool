/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.MeasureDensity

/-! # The weighted volume in an arbitrary smooth chart

If `μ` has density `e^{-V} √det g` in the charts `chartAt x₀` (`IsWeightedVolume`), then it has
density `e^{-V∘Ξ⁻¹} chartDensity Ξ` in any `C¹` chart `Ξ` (with `C¹` inverse).
-/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

theorem measurableSet_inter_preimage_of_continuousOn {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {f : X → Y} {s : Set X} (hs : MeasurableSet s) (hf : ContinuousOn f s)
    {B : Set Y} (hB : MeasurableSet B) : MeasurableSet (s ∩ f ⁻¹' B) := by
  have h1 : Measurable (s.domRestrict f) := (continuousOn_iff_continuous_domRestrict.1
      hf).measurable
  have h2 := hs.subtype_image (h1 hB)
  convert h2 using 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right]
  constructor
  · rintro ⟨hx, hfx⟩; exact ⟨hx, hfx⟩
  · rintro ⟨hx, hfx⟩; exact ⟨hx, hfx⟩

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- Mass of a piece of a chart domain, computed in the chart `Ξ`. -/
theorem local_chart_mass {V : M → ℝ} {μ : Measure M} (hμ : IsWeightedVolume F μ V)
    (Ξ : OpenPartialHomeomorph M F)
    (hΞ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ Ξ.source)
    (hΞ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ.symm Ξ.target)
    (x₀ : M) {U : Set M} (hU : IsOpen U) (hUS : U ⊆ Ξ.source)
    (hUφ : U ⊆ (chartAt F x₀).source) {B : Set F} (hB : MeasurableSet B) :
    μ (U ∩ Ξ ⁻¹' B) = ∫⁻ w in B ∩ Ξ '' U,
      ENNReal.ofReal (Real.exp (-V (Ξ.symm w)) * chartDensity Ξ w) := by
  set φ := chartAt F x₀ with hφdef
  have hφ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 φ.symm φ.target :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, F)) (n := 1) (x := x₀))
  set C := U ∩ Ξ ⁻¹' B with hC
  have hCm : MeasurableSet C :=
    measurableSet_inter_preimage_of_continuousOn hU.measurableSet (Ξ.continuousOn.mono hUS) hB
  have hCU : C ⊆ U := inter_subset_left
  have hCφ : C ⊆ φ.source := hCU.trans hUφ
  have hφCm : MeasurableSet (φ '' C) := by
    rw [φ.image_eq_target_inter_inv_preimage hCφ]
    exact measurableSet_inter_preimage_of_continuousOn φ.open_target.measurableSet
      φ.continuousOn_symm hCm
  have hφCt : φ '' C ⊆ φ.target := fun z ⟨x, hx, hxz⟩ => hxz ▸ φ.map_source (hCφ hx)
  -- mass in the chart φ
  have h1 : μ C = ∫⁻ z in φ '' C, ENNReal.ofReal (Real.exp (-V (φ.symm z)) *
      chartVolumeDensity F x₀ z) := by
    have hm : AEMeasurable φ (μ.restrict φ.source) :=
      φ.continuousOn.aemeasurable φ.open_source.measurableSet
    have := congrArg (fun ν => ν (φ '' C)) (hμ x₀)
    rw [Measure.map_apply_of_aemeasurable hm hφCm, Measure.restrict_apply'
        φ.open_source.measurableSet,
      withDensity_apply _ hφCm, Measure.restrict_restrict hφCm,
      inter_eq_left.2 hφCt] at this
    rw [(φ.injOn).preimage_image_inter hCφ] at this
    exact this
  set T : F → F := fun z => Ξ (φ.symm z) with hT
  have hpt : ∀ z ∈ φ '' C, φ.symm z ∈ C := by
    rintro z ⟨x, hx, rfl⟩
    rwa [φ.left_inv (hCφ hx)]
  have h2 : ∀ z ∈ φ '' C, ENNReal.ofReal (Real.exp (-V (φ.symm z)) * chartVolumeDensity F x₀ z) =
      ENNReal.ofReal |(fderiv ℝ T z).det| *
        ENNReal.ofReal (Real.exp (-V (Ξ.symm (T z))) * chartDensity Ξ (T z)) := by
    intro z hz
    have hx := hpt z hz
    have hxS : φ.symm z ∈ Ξ.source := hUS (hCU hx)
    have hsy : Ξ.symm (T z) = φ.symm z := Ξ.left_inv hxS
    rw [← ENNReal.ofReal_mul (abs_nonneg _), hsy, chartVolumeDensity_eq_chartDensity,
      chartDensity_transition φ Ξ hφ' hΞ hΞ' (hφCt hz) hxS]
    congr 1
    ring
  have hInj : InjOn T (φ '' C) := by
    intro z hz z' hz' h
    have h1 := hpt z hz
    have h2 := hpt z' hz'
    have : φ.symm z = φ.symm z' := Ξ.injOn (hUS (hCU h1)) (hUS (hCU h2)) h
    exact φ.symm.injOn (hφCt hz) (hφCt hz') this
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hφCm
    (f := T) (f' := fun z => fderiv ℝ T z) (fun z hz =>
      (differentiableAt_transition φ Ξ hφ' hΞ (hφCt hz)
        (hUS (hCU (hpt z hz)))).hasFDerivAt.hasFDerivWithinAt) hInj
    (fun w => ENNReal.ofReal (Real.exp (-V (Ξ.symm w)) * chartDensity Ξ w))
  have h4 : T '' (φ '' C) = B ∩ Ξ '' U := by
    rw [← image_comp]
    have : T ∘ φ = Ξ ∘ (φ.symm ∘ φ) := rfl
    have h5 : (T ∘ φ) '' C = Ξ '' C := by
      refine image_congr fun x hx => ?_
      simp only [Function.comp, hT]
      rw [φ.left_inv (hCφ hx)]
    rw [h5, hC, image_inter_preimage, inter_comm]
  rw [h1, setLIntegral_congr_fun hφCm h2, ← hcv, h4]


omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- **Density of the weighted volume in an arbitrary `C¹` chart.** -/
theorem map_chart_density [SecondCountableTopology M] {V : M → ℝ} {μ : Measure M}
    (hμ : IsWeightedVolume F μ V) (Ξ : OpenPartialHomeomorph M F)
    (hΞ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ Ξ.source)
    (hΞ' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ.symm Ξ.target) :
    (μ.restrict Ξ.source).map Ξ = (volume.restrict Ξ.target).withDensity
      fun w => ENNReal.ofReal (Real.exp (-V (Ξ.symm w)) * chartDensity Ξ w) := by
  set S := Ξ.source with hS
  set g : F → ℝ≥0∞ := fun w => ENNReal.ofReal (Real.exp (-V (Ξ.symm w)) * chartDensity Ξ w)
    with hg
  have hmΞ : AEMeasurable Ξ (μ.restrict S) := Ξ.continuousOn.aemeasurable
      Ξ.open_source.measurableSet
  obtain ⟨t, hts, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := S)
    (f := fun x => (chartAt F x).source) (fun x _ =>
      mem_nhdsWithin_of_mem_nhds ((chartAt F x).open_source.mem_nhds (mem_chart_source F x)))
  have : Countable t := htc.to_subtype
  set U : t → Set M := fun i => S ∩ (chartAt F (i : M)).source with hU
  have hUo : ∀ i, IsOpen (U i) := fun i => Ξ.open_source.inter (chartAt F (i : M)).open_source
  have hUcov : ⋃ i, U i = S := by
    refine subset_antisymm (iUnion_subset fun i => inter_subset_left) fun x hx => ?_
    have := hcov hx
    simp only [mem_iUnion] at this
    obtain ⟨y, hy, hxy⟩ := this
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hx, hxy⟩
  have himg : ⋃ i, Ξ '' U i = Ξ.target := by
    rw [← image_iUnion, hUcov]
    exact Ξ.image_source_eq_target
  have hpiece : ∀ i, ((μ.restrict S).map Ξ).restrict (Ξ '' U i) =
      ((volume.restrict Ξ.target).withDensity g).restrict (Ξ '' U i) := by
    intro i
    have hopen : IsOpen (Ξ '' U i) := Ξ.isOpen_image_of_subset_source (hUo i) inter_subset_left
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
      Measure.map_apply_of_aemeasurable hmΞ (hB.inter hopen.measurableSet),
      Measure.restrict_apply' Ξ.open_source.measurableSet, withDensity_apply _ (hB.inter
          hopen.measurableSet),
      Measure.restrict_restrict (hB.inter hopen.measurableSet)]
    have h1 : Ξ ⁻¹' (B ∩ Ξ '' U i) ∩ S = U i ∩ Ξ ⁻¹' B := by
      have hh := Ξ.injOn.preimage_image_inter (inter_subset_left : U i ⊆ S)
      have hx : ∀ x, (x ∈ S ∧ Ξ x ∈ Ξ '' U i) ↔ x ∈ U i := fun x =>
        ⟨fun h => (Set.ext_iff.1 hh x).1 ⟨h.2, h.1⟩,
         fun h => ⟨((Set.ext_iff.1 hh x).2 h).2, ((Set.ext_iff.1 hh x).2 h).1⟩⟩
      ext x
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨⟨hB, hI⟩, hSx⟩
        exact ⟨(hx x).1 ⟨hSx, hI⟩, hB⟩
      · rintro ⟨hUx, hB⟩
        have := (hx x).2 hUx
        exact ⟨⟨hB, this.2⟩, this.1⟩
    have h2 : B ∩ Ξ '' U i ∩ Ξ.target = B ∩ Ξ '' U i := by
      refine inter_eq_left.2 ?_
      exact inter_subset_right.trans ((Set.image_mono (inter_subset_left : U i ⊆ S)).trans
        Ξ.image_source_eq_target.subset)
    rw [h1, h2]
    have := local_chart_mass hμ Ξ hΞ hΞ' (i : M) (hUo i) inter_subset_left
      inter_subset_right hB
    exact this
  have hcongr := Measure.restrict_iUnion_congr.2 hpiece
  rw [himg] at hcongr
  have hae1 : ∀ᵐ w ∂((μ.restrict S).map Ξ), w ∈ Ξ.target := by
    refine (ae_map_iff hmΞ (p := fun w => w ∈ Ξ.target) Ξ.open_target.measurableSet).2 ?_
    rw [ae_restrict_iff' Ξ.open_source.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => Ξ.map_source hx
  have hae2 : ∀ᵐ w ∂((volume.restrict Ξ.target).withDensity g), w ∈ Ξ.target :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem Ξ.open_target.measurableSet)
  rw [← Measure.restrict_eq_self_of_ae_mem hae1, hcongr, Measure.restrict_eq_self_of_ae_mem hae2]

end CutCur
