/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPDensity
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-! # The density of weighted Riemannian volume

The change of variables in the inverse chart identifies the chart definition of weighted
volume with an exponential density against canonical Riemannian volume.
-/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace CutCur

open TauCeti TauCeti.Manifold

/-- Equality of chart pushforwards determines the measures restricted to the chart source. -/
theorem chart_map_restrict_injective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (e : OpenPartialHomeomorph X Y) {μ ν : Measure X}
    (h : (μ.restrict e.source).map e = (ν.restrict e.source).map e) :
    μ.restrict e.source = ν.restrict e.source := by
  have embedding := e.isOpenEmbedding_restrict.measurableEmbedding
  have map_source (m : Measure X) : (m.restrict e.source).map e =
      (m.comap (Subtype.val : e.source → X)).map (e.source.domRestrict e) := by
    have meas : AEMeasurable e (m.restrict e.source) :=
      e.continuousOn.aemeasurable e.open_source.measurableSet
    rw [← map_comap_subtype_coe e.open_source.measurableSet] at meas ⊢
    exact meas.map_map_of_aemeasurable measurable_subtype_coe.aemeasurable
  rw [map_source, map_source] at h
  rw [← map_comap_subtype_coe e.open_source.measurableSet,
    ← map_comap_subtype_coe e.open_source.measurableSet, embedding.map_injective h]

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)] in
/-- Push forward the canonical weighted volume in a chart with a `C¹` inverse. -/
theorem map_canonical_weighted_volume_chart [LindelofSpace M] (V : M → ℝ)
    (Ξ : OpenPartialHomeomorph M F)
    (hΞ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ.symm Ξ.target) :
    (((riemannianVolume 𝓘(ℝ, F) M).withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (-V x)))).restrict Ξ.source).map Ξ =
      (volume.restrict Ξ.target).withDensity fun w ↦ ENNReal.ofReal
        (Real.exp (-V (Ξ.symm w)) *
          riemannianJacobian (I := 𝓘(ℝ, F)) (stdOrthonormalBasis ℝ F).toBasis Ξ.symm w) := by
  ext B hB
  have hpre : MeasurableSet (Ξ ⁻¹' B ∩ Ξ.source) :=
    Ξ.continuousOn.measurableSet_preimage_inter Ξ.open_source.measurableSet hB
  have hmeas := Ξ.continuousOn.aemeasurable
    (μ := (riemannianVolume 𝓘(ℝ, F) M).withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-V x))))
    Ξ.open_source.measurableSet
  rw [Measure.map_apply_of_aemeasurable hmeas hB,
    Measure.restrict_apply' Ξ.open_source.measurableSet,
    withDensity_apply _ hpre, withDensity_apply _ hB, Measure.restrict_restrict hB]
  have himage : Ξ.symm '' (B ∩ Ξ.target) = Ξ ⁻¹' B ∩ Ξ.source := by
    ext x
    constructor
    · rintro ⟨z, ⟨hzB, hzt⟩, rfl⟩
      exact ⟨by rwa [mem_preimage, Ξ.right_inv hzt], Ξ.map_target hzt⟩
    · rintro ⟨hxB, hxs⟩
      exact ⟨Ξ x, ⟨hxB, Ξ.map_source hxs⟩, Ξ.left_inv hxs⟩
  let b := stdOrthonormalBasis ℝ F
  have hBt := hB.inter Ξ.open_target.measurableSet
  have hcov := b.toBasis.setLIntegral_riemannianVolume_image_of_injOn (I := 𝓘(ℝ, F)) rfl
    hBt (Ξ.symm.injOn.mono inter_subset_right)
    (fun z hz ↦ (hΞ.contMDiffAt (Ξ.open_target.mem_nhds hz.2)).mdifferentiableAt one_ne_zero)
    (fun x ↦ ENNReal.ofReal (Real.exp (-V x)))
  rw [himage, b.addHaar_eq_volume] at hcov
  rw [hcov]
  refine setLIntegral_congr_fun hBt fun z _ ↦ ?_
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)] in
private theorem weightedVolume_restrict_chart [LindelofSpace M] {μ : Measure M} {V : M → ℝ}
    (hμ : IsWeightedVolume F μ V) (α : M) :
    μ.restrict (chartAt F α).source = ((riemannianVolume 𝓘(ℝ, F) M).withDensity
      fun x ↦ ENNReal.ofReal (Real.exp (-V x))).restrict (chartAt F α).source := by
  let e := chartAt F α
  let ν := (riemannianVolume 𝓘(ℝ, F) M).withDensity
    fun x ↦ ENNReal.ofReal (Real.exp (-V x))
  have hchart : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 e.symm e.target := by
    have hd := contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, F)) (n := 1) α
    simpa [e, extChartAt, OpenPartialHomeomorph.extend] using hd
  have hmap : (μ.restrict e.source).map e = (ν.restrict e.source).map e := by
    rw [show (ν.restrict e.source).map e = _ from map_canonical_weighted_volume_chart F V e hchart]
    change (μ.restrict (chartAt F α).source).map (chartAt F α) = _
    rw [hμ α]
    simp only [chartVolumeDensity_eq_jacobian, e]
  exact chart_map_restrict_injective e hmap

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)] in
/-- The chart definition is the exponential density against canonical Riemannian volume. -/
theorem eq_riemannianVolume_withDensity [LindelofSpace M] {μ : Measure M} {V : M → ℝ}
    (hμ : IsWeightedVolume F μ V) :
    μ = (riemannianVolume 𝓘(ℝ, F) M).withDensity fun x ↦ ENNReal.ofReal (Real.exp (-V x)) := by
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover (fun x : M ↦ (chartAt F x).source)
    (chart_source_mem_nhds F)
  have h := (Measure.restrict_biUnion_congr ht).2
    (fun x _ ↦ weightedVolume_restrict_chart F hμ x)
  simpa only [hcover, Measure.restrict_univ] using h

end CutCur
