/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.MeasureDensity
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPGreen
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-! # The weighted volume in an arbitrary smooth chart

If `μ` has density `e^{-V} √det g` in the charts `chartAt x₀` (`IsWeightedVolume`), then it has
density `e^{-V∘Ξ⁻¹} chartDensity Ξ` in any chart `Ξ` with smooth inverse of order one.
-/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutCur

theorem measurableSet_inter_preimage_of_continuousOn {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {f : X → Y} {s : Set X} (hs : MeasurableSet s) (hf : ContinuousOn f s)
    {B : Set Y} (hB : MeasurableSet B) : MeasurableSet (s ∩ f ⁻¹' B) := by
  simpa only [inter_comm] using hf.measurableSet_preimage_inter hs hB

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- Density of the weighted measure in a chart with a `C¹` inverse. -/
theorem map_chart_density [LindelofSpace M] {V : M → ℝ} {μ : Measure M}
    (hμ : IsWeightedVolume F μ V) (Ξ : OpenPartialHomeomorph M F)
    (hΞ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) 1 Ξ.symm Ξ.target) :
    (μ.restrict Ξ.source).map Ξ = (volume.restrict Ξ.target).withDensity
      fun w ↦ ENNReal.ofReal (Real.exp (-V (Ξ.symm w)) * chartDensity Ξ w) := by
  ext B hB
  have hpre : MeasurableSet (Ξ ⁻¹' B ∩ Ξ.source) :=
    Ξ.continuousOn.measurableSet_preimage_inter Ξ.open_source.measurableSet hB
  have hmeas := Ξ.continuousOn.aemeasurable (μ := μ) Ξ.open_source.measurableSet
  rw [Measure.map_apply_of_aemeasurable hmeas hB,
    Measure.restrict_apply' Ξ.open_source.measurableSet, eq_riemannianVolume_withDensity F hμ,
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
  rw [← chartDensity_eq_jacobian, ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]

end CutCur
