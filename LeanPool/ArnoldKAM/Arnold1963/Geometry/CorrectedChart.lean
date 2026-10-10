/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.FrequencyChart

/-!
Construct the corrected analytic chart from the original chart and a small frequency shift,
including local two-sided inverse identities.
-/

@[expose] public section
noncomputable section
open Set Function Filter Metric
open scoped NNReal Topology
namespace KamProject.Arnold1963

theorem correctedFrequency_chart {n : ℕ}
    {A g Δ : ComplexSpace n → ComplexSpace n} {G Ω H V U : Set (ComplexSpace n)}
    {β κ : ℝ≥0} (c : AnalyticFrequencyChart A g G Ω)
    (d : FrequencyShiftData (Δ ∘ g) V β κ)
    (hV : V ⊆ Ω) (hgV : MapsTo g V H) (hHG : H ⊆ G)
    (hΔ : AnalyticOnNhd ℂ Δ H) (hVc : ConjInvariant V)
    (hΔc : ∀ p ∈ H, Δ (conjVec p) = conjVec (Δ p))
    (hU : IsCompact U) (hUc : ConjInvariant U) (hUt : U ⊆ frequencyInverseTarget V β) :
    AnalyticFrequencyChart (fun p => A p + Δ p) (correctedFrequencyInverse g Δ V β)
      (correctedFrequencyInverse g Δ V β '' U) U := by
  let B := correctedFrequencyInverse g Δ V β
  have hb : AnalyticOnNhd ℂ B U :=
    fun y hy => correctedFrequencyInverse_analytic d (c.inverse_analytic.mono hV) y (hUt hy)
  have hmap : ∀ y ∈ U, B y ∈ H := fun y hy =>
    hgV (erosion_subset _ _ (d.inverse_spec (hUt hy)).1)
  have hr : ∀ y ∈ U, A (B y) + Δ (B y) = y :=
    fun y hy => correctedFrequencyInverse_right d (fun x hx => c.right (hV hx)) (hUt hy)
  have ha : ∀ x ∈ V, (Δ ∘ g) (conjVec x) = conjVec ((Δ ∘ g) x) := by
    intro x hx
    dsimp only [Function.comp_apply]
    rw [c.inverse_conj (hV hx), hΔc _ (hgV hx)]
  have hbc : ∀ y ∈ U, B (conjVec y) = conjVec (B y) := by
    intro y hy
    change g (frequencyInverse (Δ ∘ g) V β (conjVec y)) =
      conjVec (g (frequencyInverse (Δ ∘ g) V β y))
    rw [d.inverse_conj hVc ha (hUt hy),
      c.inverse_conj (hV (erosion_subset _ _ (d.inverse_spec (hUt hy)).1))]
  refine ⟨hU.image_of_continuousOn hb.continuousOn, ?_, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨y, hy, rfl⟩
    exact (c.analytic _ (hHG (hmap y hy))).add (hΔ _ (hmap y hy))
  · rintro p ⟨y, hy, rfl⟩
    change A (B y) + Δ (B y) ∈ U
    rwa [hr y hy]
  · intro y hy
    exact mem_image_of_mem B hy
  · rintro p ⟨y, hy, rfl⟩
    let x := frequencyInverse (Δ ∘ g) V β y
    have hxV : x ∈ V := erosion_subset _ _ (d.inverse_spec (hUt hy)).1
    have hp : B y ∈ G := hHG (hmap y hy)
    have hAx : A (B y) = x := c.right (hV hxV)
    have ht : Tendsto A (𝓝 (B y)) (𝓝 x) := by
      rw [← hAx]
      exact (c.analytic _ hp).continuousAt
    have hs : ∀ᶠ q in 𝓝 (B y), A q ∈ frequencyInverseSource V β :=
      ht (erosion_mem_nhds d.radius_pos (d.inverse_spec (hUt hy)).1)
    filter_upwards [c.left_local _ hp, hs] with q hq hqs
    change g (frequencyInverse (Δ ∘ g) V β (A q + Δ q)) = q
    have he : A q + Δ q = frequencyShift (Δ ∘ g) (A q) := by
      simp only [frequencyShift, Function.comp_apply, hq]
    rw [he]
    change g (invFunOn (frequencyShift (Δ ∘ g)) (frequencyInverseSource V β)
      (frequencyShift (Δ ∘ g) (A q))) = q
    rw [d.shift_injOn.leftInvOn_invFunOn hqs, hq]
  · intro y hy
    have hi := d.inverse_analytic_right (hUt hy)
    have hxΩ := hV (erosion_subset _ _ (d.inverse_spec (hUt hy)).1)
    have hh : ∀ᶠ z in 𝓝 y, A (g (frequencyInverse (Δ ∘ g) V β z)) =
        frequencyInverse (Δ ∘ g) V β z := hi.1.continuousAt (c.right_local _ hxΩ)
    filter_upwards [hh, hi.2] with z hz he
    change A (g (frequencyInverse (Δ ∘ g) V β z)) +
      Δ (g (frequencyInverse (Δ ∘ g) V β z)) = z
    rw [hz]
    exact he
  · rintro p ⟨y, hy, rfl⟩
    exact ⟨conjVec y, hUc _ hy, hbc y hy⟩
  · rintro p ⟨y, hy, rfl⟩
    rw [c.map_conj _ (hHG (hmap y hy)), hΔc _ (hmap y hy)]
    simp only [conjVec_eq_star, star_add, B]

end KamProject.Arnold1963
