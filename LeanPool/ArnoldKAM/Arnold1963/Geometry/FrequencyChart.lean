/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.DomainCover
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.FrequencyChange

/-!
Analytic frequency charts on compact domains. Local inverse identities imply the required
coverage and inverse derivative estimates.
-/

@[expose] public section
noncomputable section
open Set Function Filter Metric
open scoped NNReal Topology
namespace KamProject.Arnold1963

/-- An analytic frequency chart with an analytic inverse and specified source and target sets. -/
structure AnalyticFrequencyChart {n : ℕ} (A g : ComplexSpace n → ComplexSpace n)
    (G Ω : Set (ComplexSpace n)) : Prop where
  compact : IsCompact G
  analytic : AnalyticOnNhd ℂ A G
  inverse_analytic : AnalyticOnNhd ℂ g Ω
  maps : MapsTo A G Ω
  inverse_maps : MapsTo g Ω G
  left_local : ∀ p ∈ G, ∀ᶠ x in 𝓝 p, g (A x) = x
  right_local : ∀ y ∈ Ω, ∀ᶠ x in 𝓝 y, A (g x) = x
  domain_conj : ConjInvariant G
  map_conj : ∀ p ∈ G, A (conjVec p) = conjVec (A p)

namespace AnalyticFrequencyChart
variable {n : ℕ} {A g : ComplexSpace n → ComplexSpace n}
  {G Ω : Set (ComplexSpace n)} (c : AnalyticFrequencyChart A g G Ω)
include c

theorem left {p} (hp : p ∈ G) : g (A p) = p := (c.left_local p hp).self_of_nhds
theorem right {y} (hy : y ∈ Ω) : A (g y) = y := (c.right_local y hy).self_of_nhds

theorem image_eq : A '' G = Ω := by
  apply Subset.antisymm c.maps.image_subset
  intro y hy
  exact ⟨g y, c.inverse_maps hy, c.right hy⟩

theorem inverse_image_eq : g '' Ω = G := by
  apply Subset.antisymm c.inverse_maps.image_subset
  intro p hp
  exact ⟨A p, c.maps hp, c.left hp⟩

theorem image_compact : IsCompact Ω := by
  rw [← c.image_eq]
  exact c.compact.image_of_continuousOn c.analytic.continuousOn

theorem injOn : InjOn A G := by
  intro p hp q hq he
  rw [← c.left hp, ← c.left hq, he]

theorem image_conj : ConjInvariant Ω := by
  intro y hy
  rw [← c.right hy, ← c.map_conj _ (c.inverse_maps hy)]
  exact c.maps (c.domain_conj _ (c.inverse_maps hy))

theorem inverse_conj {y} (hy : y ∈ Ω) : g (conjVec y) = conjVec (g y) := by
  apply c.injOn (c.inverse_maps (c.image_conj _ hy)) (c.domain_conj _ (c.inverse_maps hy))
  rw [c.right (c.image_conj _ hy), c.map_conj _ (c.inverse_maps hy), c.right hy]

theorem symm : AnalyticFrequencyChart g A Ω G where
  compact := c.image_compact
  analytic := c.inverse_analytic
  inverse_analytic := c.analytic
  maps := c.inverse_maps
  inverse_maps := c.maps
  left_local := c.right_local
  right_local := c.left_local
  domain_conj := c.image_conj
  map_conj := fun _ hy => c.inverse_conj hy

theorem interior_back {p} (hp : p ∈ G) (hy : A p ∈ interior Ω) : p ∈ interior G :=
  mem_interior_of_local_inverse (c.analytic _ hp).continuousAt c.inverse_maps
    (c.left_local p hp) hy

theorem inverse_maps_erosion {Θ β : ℝ≥0} (hΘ : 0 < Θ)
    (hd : ∀ p ∈ G, ‖fderiv ℂ A p‖ ≤ Θ) :
    MapsTo g (erosion Ω (Θ * β)) (erosion G β) := by
  intro y hy
  have hyΩ := erosion_subset _ _ hy
  apply mem_erosion_of_image_buffer c.compact.isClosed hΘ c.analytic hd
    (fun p hp => c.interior_back hp) (c.inverse_maps hyΩ)
  simpa only [c.right hyΩ] using hy

theorem erosion_subset_image {Θ β : ℝ≥0} (hΘ : 0 < Θ)
    (hd : ∀ p ∈ G, ‖fderiv ℂ A p‖ ≤ Θ) :
    erosion Ω (Θ * β) ⊆ A '' erosion G β := by
  intro y hy
  exact ⟨g y, c.inverse_maps_erosion hΘ hd hy, c.right (erosion_subset _ _ hy)⟩

theorem inverse_derivative_le {θ : ℝ} (hθ : 0 < θ)
    (hlo : ∀ p ∈ G, ∀ v, θ * ‖v‖ ≤ ‖fderiv ℂ A p v‖)
    {y} (hy : y ∈ Ω) : ‖fderiv ℂ g y‖ ≤ θ⁻¹ := by
  have hd := ((c.analytic _ (c.inverse_maps hy)).differentiableAt.hasFDerivAt.comp y
    (c.inverse_analytic _ hy).differentiableAt.hasFDerivAt)
  have hid : (fderiv ℂ A (g y)).comp (fderiv ℂ g y) = ContinuousLinearMap.id ℂ _ :=
    (hd.congr_of_eventuallyEq (Filter.EventuallyEq.symm (c.right_local y hy))).unique
      (hasFDerivAt_id y)
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hθ.le)
  intro v
  have hh := hlo _ (c.inverse_maps hy) (fderiv ℂ g y v)
  have hv := DFunLike.congr_fun hid v
  change fderiv ℂ A (g y) (fderiv ℂ g y v) = v at hv
  rw [hv] at hh
  calc
    ‖fderiv ℂ g y v‖ ≤ ‖v‖ / θ := (le_div_iff₀ hθ).mpr (by simpa [mul_comm] using hh)
    _ = θ⁻¹ * ‖v‖ := by rw [div_eq_mul_inv, mul_comm]

theorem restrict {S : Set (ComplexSpace n)} (hS : S ⊆ Ω) (hSc : IsCompact S)
    (hSj : ConjInvariant S) : AnalyticFrequencyChart A g (g '' S) S := by
  refine ⟨hSc.image_of_continuousOn (c.inverse_analytic.mono hS).continuousOn,
    c.analytic.mono (image_subset_iff.mpr (fun _ hx => c.inverse_maps (hS hx))),
    c.inverse_analytic.mono hS, ?_, fun _ hx => mem_image_of_mem g hx, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rwa [c.right (hS hy)]
  · rintro _ ⟨y, hy, rfl⟩
    exact c.left_local _ (c.inverse_maps (hS hy))
  · intro y hy
    exact c.right_local y (hS hy)
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨conjVec y, hSj _ hy, c.inverse_conj (hS hy)⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact c.map_conj _ (c.inverse_maps (hS hy))

end AnalyticFrequencyChart
end KamProject.Arnold1963
