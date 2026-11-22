/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPDensity

/-! # Full support of the weighted volume

If `μ` is `IsWeightedVolume` and the chart volume density is continuous and positive on every
chart target, then `μ` charges every nonempty open set.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

namespace CutCur

section Support

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

theorem measure_pos_of_isWeightedVolume {μ : Measure M} {V : M → ℝ} (hV : MSmooth F V)
    (hμ : IsWeightedVolume F μ V)
    (hcont : ∀ x₀ : M, ContinuousOn (chartVolumeDensity F x₀) (chartAt F x₀).target)
    (hpd : ∀ (x₀ : M) (z : F), z ∈ (chartAt F x₀).target → 0 < chartVolumeDensity F x₀ z)
    {U : Set M} (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U := by
  obtain ⟨x₀, hx₀⟩ := hne
  set φ := chartAt F x₀ with hφ
  have hx₀s : x₀ ∈ φ.source := mem_chart_source F x₀
  set W := U ∩ φ.source with hW
  have hWo : IsOpen W := hU.inter φ.open_source
  set A := φ '' W with hA
  have hAo : IsOpen A := φ.isOpen_image_of_subset_source hWo inter_subset_right
  have hAne : A.Nonempty := ⟨φ x₀, x₀, ⟨hx₀, hx₀s⟩, rfl⟩
  have hAt : A ⊆ φ.target := fun z ⟨y, hy, hyz⟩ => hyz ▸ φ.map_source hy.2
  by_contra hcon
  have hU0 : μ U = 0 := le_antisymm (not_lt.mp hcon) bot_le
  have hW0 : μ W = 0 := measure_mono_null inter_subset_left hU0
  have h := hμ x₀
  have hL : ((μ.restrict φ.source).map φ) A = 0 := by
    have hae : AEMeasurable φ (μ.restrict φ.source) :=
      φ.continuousOn.aemeasurable φ.open_source.measurableSet
    rw [Measure.map_apply_of_aemeasurable hae hAo.measurableSet, Measure.restrict_apply'
      φ.open_source.measurableSet]
    refine measure_mono_null (fun y ⟨hy1, hy2⟩ => ?_) hW0
    obtain ⟨y', hy', hyy⟩ := hy1
    have : y' = y := φ.injOn hy'.2 hy2 hyy
    exact this ▸ hy'
  rw [h] at hL
  set d : F → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-V (φ.symm z)) * chartVolumeDensity F x₀ z) with hd
  rw [withDensity_apply' _ A, Measure.restrict_restrict hAo.measurableSet,
    inter_eq_left.mpr hAt] at hL
  have hdc : ContinuousOn d A := by
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.mul ?_ ((hcont x₀).mono hAt)
    refine (Real.continuous_exp.comp_continuousOn ?_)
    exact (hV.continuous.comp_continuousOn (φ.continuousOn_symm.mono hAt)).neg
  have hae : AEMeasurable d (volume.restrict A) := hdc.aemeasurable hAo.measurableSet
  have h0 := (lintegral_eq_zero_iff' hae).mp hL
  rw [Filter.EventuallyEq, ae_restrict_iff' hAo.measurableSet] at h0
  have hvol : 0 < volume A := hAo.measure_pos volume hAne
  have : volume A = 0 := by
    refine measure_mono_null (fun z hz => ?_) (ae_iff.mp h0)
    simp only [Set.mem_ofPred_eq, not_imp]
    refine ⟨hz, ?_⟩
    have := hpd x₀ z (hAt hz)
    simp only [Pi.zero_apply, hd]
    exact (ENNReal.ofReal_pos.mpr (mul_pos (Real.exp_pos _) this)).ne'
  exact absurd this hvol.ne'

variable [IsManifold 𝓘(ℝ, F) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]

/-- The canonical weighted measure charges every nonempty open set. -/
theorem isOpenPosMeasure_of_weighted {μ : Measure M} {V : M → ℝ} (hV : MSmooth F V)
    (hμ : IsWeightedVolume F μ V) : μ.IsOpenPosMeasure :=
  ⟨fun U hU hne => (measure_pos_of_isWeightedVolume F hV hμ (continuousOn_chartVolumeDensity F)
    (fun x z hz => chartVolumeDensity_pos F x (z := z) hz) (U := U) hU hne).ne'⟩

end Support

end CutCur
