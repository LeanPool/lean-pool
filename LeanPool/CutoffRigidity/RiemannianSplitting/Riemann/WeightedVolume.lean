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

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)] in
private theorem weightedVolume_restrict_chart [LindelofSpace M] {μ : Measure M} {V : M → ℝ}
    (hμ : IsWeightedVolume F μ V) (α : M) :
    μ.restrict (chartAt F α).source = ((riemannianVolume 𝓘(ℝ, F) M).withDensity
      fun x ↦ ENNReal.ofReal (Real.exp (-V x))).restrict (chartAt F α).source := by
  let e := chartAt F α
  ext s hs
  let A : Set F := e.symm ⁻¹' s ∩ e.target
  have hA : MeasurableSet A := e.continuousOn_symm.measurableSet_preimage_inter
    e.open_target.measurableSet hs
  have hAt : A ⊆ e.target := inter_subset_right
  have himage : e.symm '' A = s ∩ e.source := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz.1, e.map_target hz.2⟩
    · rintro ⟨hx, hxs⟩
      exact ⟨e x, ⟨by rwa [mem_preimage, e.left_inv hxs], e.map_source hxs⟩, e.left_inv hxs⟩
  have hpreimage : e ⁻¹' A ∩ e.source = s ∩ e.source := by
    ext x
    simp only [A, mem_preimage, mem_inter_iff]
    constructor
    · rintro ⟨⟨hx, _⟩, hxs⟩
      exact ⟨by simpa only [e.left_inv hxs] using hx, hxs⟩
    · rintro ⟨hx, hxs⟩
      exact ⟨⟨by simpa only [e.left_inv hxs] using hx, e.map_source hxs⟩, hxs⟩
  have hmap : (μ.restrict e.source).map e A = μ (s ∩ e.source) := by
    rw [Measure.map_apply_of_aemeasurable
      (e.continuousOn.aemeasurable e.open_source.measurableSet) hA,
      Measure.restrict_apply' e.open_source.measurableSet, hpreimage]
  rw [hμ α, withDensity_apply _ hA, Measure.restrict_restrict hA, inter_eq_left.mpr hAt] at hmap
  let b := stdOrthonormalBasis ℝ F
  have hd : ∀ z ∈ A, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) e.symm z := by
    intro z hz
    have ht : (extChartAt 𝓘(ℝ, F) α).target = e.target := by
      simp [e, extChartAt, OpenPartialHomeomorph.extend]
    have htarget : (extChartAt 𝓘(ℝ, F) α).target ∈ 𝓝 z :=
      ht ▸ e.open_target.mem_nhds (hAt hz)
    exact ((contMDiffOn_extChartAt_symm (n := 1) α).contMDiffAt htarget).mdifferentiableAt
      one_ne_zero
  have hcov := b.toBasis.setLIntegral_riemannianVolume_image_of_injOn (I := 𝓘(ℝ, F)) rfl
    hA (e.symm.injOn.mono hAt) hd (fun x ↦ ENNReal.ofReal (Real.exp (-V x)))
  rw [himage, b.addHaar_eq_volume] at hcov
  simp only [Measure.restrict_apply hs]
  rw [withDensity_apply _ (hs.inter e.open_source.measurableSet), hcov, ← hmap]
  refine setLIntegral_congr_fun hA fun z _ ↦ ?_
  rw [← chartVolumeDensity_eq_jacobian F α z, ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]

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
