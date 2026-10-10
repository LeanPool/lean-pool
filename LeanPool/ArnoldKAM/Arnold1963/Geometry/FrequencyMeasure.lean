/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.FrequencyChart
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.RealJacobian

/-!
Pull back real-slice measure through the original frequency chart, using real Jacobians.
-/

@[expose] public section
noncomputable section
open Set Function MeasureTheory
open scoped ENNReal
namespace KamProject.Arnold1963
namespace AnalyticFrequencyChart
variable {n : ℕ} {A g : ComplexSpace n → ComplexSpace n}
  {G Ω : Set (ComplexSpace n)} (c : AnalyticFrequencyChart A g G Ω)
include c

theorem inverse_real {x : RealSpace n} (hx : complexify x ∈ Ω) :
    complexify (realPart (g (complexify x))) = g (complexify x) := by
  apply complexify_realPart_of_conj
  simpa only [conjVec_complexify] using (c.inverse_conj hx).symm

theorem realSlice_inverse_image {S : Set (ComplexSpace n)} (hS : S ⊆ Ω) :
    realSlice (g '' S) = realRestriction g '' realSlice S := by
  ext p
  constructor
  · rintro ⟨y, hy, he⟩
    have hyΩ := hS hy
    have hgy := c.inverse_maps hyΩ
    have heA : A (complexify p) = y := by rw [← he, c.right hyΩ]
    have hyreal : complexify (realPart y) = y := by
      apply complexify_realPart_of_conj
      rw [← heA]
      exact (c.map_conj _ (he ▸ hgy)).symm.trans (by rw [conjVec_complexify])
    refine ⟨realPart y, ?_, ?_⟩
    · change complexify (realPart y) ∈ S
      rwa [hyreal]
    · change realPart (g (complexify (realPart y))) = p
      rw [hyreal, he, realPart_complexify]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨complexify x, hx, (c.inverse_real (hS hx)).symm⟩

theorem inverse_realVolume_le {S : Set (ComplexSpace n)} (hS : MeasurableSet S)
    (hSΩ : S ⊆ Ω) {θ : ℝ} (hθ : 0 < θ)
    (hlo : ∀ p ∈ G, ∀ v, θ * ‖v‖ ≤ ‖fderiv ℂ A p v‖) :
    realVolume (g '' S) ≤ ENNReal.ofReal (θ⁻¹ ^ n) * realVolume S := by
  unfold realVolume
  rw [c.realSlice_inverse_image hSΩ]
  change volume (realRestriction g '' realSlice S) ≤ _ * volume (realSlice S)
  apply real_image_measure_le (hS.preimage (continuous_complexify n).measurable)
    (inv_nonneg.mpr hθ.le)
  · intro x hx
    exact (hasFDerivAt_realRestriction
      (c.inverse_analytic _ (hSΩ hx)).differentiableAt).differentiableAt
  · intro x hx
    rw [(hasFDerivAt_realRestriction (c.inverse_analytic _ (hSΩ hx)).differentiableAt).fderiv]
    exact (norm_realDerivative_le _).trans (c.inverse_derivative_le hθ hlo (hSΩ hx))

theorem inverse_image_complement {G₁ : Set (ComplexSpace n)} (hG₁ : G₁ ⊆ G) :
    g '' (Ω \ A '' G₁) = G \ G₁ := by
  ext p
  constructor
  · rintro ⟨y, ⟨hy, hny⟩, rfl⟩
    refine ⟨c.inverse_maps hy, ?_⟩
    intro hg
    exact hny ⟨g y, hg, c.right hy⟩
  · rintro ⟨hp, hnp⟩
    refine ⟨A p, ⟨c.maps hp, ?_⟩, c.left hp⟩
    rintro ⟨q, hq, he⟩
    exact hnp ((c.injOn (hG₁ hq) hp he) ▸ hq)

theorem realVolume_loss_le {G₁ S : Set (ComplexSpace n)} (hG₁ : G₁ ⊆ G)
    (hS : MeasurableSet S) (hcover : S ⊆ A '' G₁) {θ : ℝ} (hθ : 0 < θ)
    (hlo : ∀ p ∈ G, ∀ v, θ * ‖v‖ ≤ ‖fderiv ℂ A p v‖) :
    realVolume (G \ G₁) ≤ ENNReal.ofReal (θ⁻¹ ^ n) * realVolume (Ω \ S) := by
  calc
    _ = realVolume (g '' (Ω \ A '' G₁)) := by rw [c.inverse_image_complement hG₁]
    _ ≤ realVolume (g '' (Ω \ S)) := realVolume_mono (image_mono (sdiff_subset_sdiff_right hcover))
    _ ≤ _ := c.inverse_realVolume_le (c.image_compact.isClosed.measurableSet.diff hS)
      sdiff_subset hθ hlo

theorem realVolume_image_le {Θ : ℝ} (hΘ : 0 ≤ Θ)
    (hhi : ∀ p ∈ G, ‖fderiv ℂ A p‖ ≤ Θ) :
    realVolume Ω ≤ ENNReal.ofReal (Θ ^ n) * realVolume G := by
  rw [← c.image_eq]
  unfold realVolume
  rw [c.symm.realSlice_inverse_image (Subset.refl G)]
  change volume (realRestriction A '' realSlice G) ≤ _ * volume (realSlice G)
  apply real_image_measure_le
    (c.compact.isClosed.measurableSet.preimage (continuous_complexify n).measurable) hΘ
  · intro x hx
    exact (hasFDerivAt_realRestriction (c.analytic _ hx).differentiableAt).differentiableAt
  · intro x hx
    rw [(hasFDerivAt_realRestriction (c.analytic _ hx).differentiableAt).fderiv]
    exact (norm_realDerivative_le _).trans (hhi _ hx)

end AnalyticFrequencyChart
end KamProject.Arnold1963
