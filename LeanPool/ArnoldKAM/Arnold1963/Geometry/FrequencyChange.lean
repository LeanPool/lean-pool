/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.FrequencyInverse

/-!
Compose the old frequency inverse with the inverse of the small shift. Domain buffers and
measure bounds are assembled in FrequencyDomain to keep the dependencies acyclic.
-/

@[expose] public section
noncomputable section
open Set Function
open scoped NNReal
namespace KamProject.Arnold1963

theorem frequencyChange_derivative_bounds {n : ℕ}
    {A Δ : ComplexSpace n → ComplexSpace n} {p : ComplexSpace n}
    {θ Θ : ℝ} {κ : ℝ≥0} (hA : DifferentiableAt ℂ A p) (hΔ : DifferentiableAt ℂ Δ p)
    (hθΘ : θ ≤ Θ) (hlo : ∀ v, θ * ‖v‖ ≤ ‖fderiv ℂ A p v‖)
    (hhi : ∀ v, ‖fderiv ℂ A p v‖ ≤ Θ * ‖v‖)
    (hdΔ : ‖fderiv ℂ Δ p‖ ≤ (κ : ℝ) * θ) (v : ComplexSpace n) :
    (θ * (1 - (κ : ℝ))) * ‖v‖ ≤ ‖fderiv ℂ (fun x => A x + Δ x) p v‖ ∧
      ‖fderiv ℂ (fun x => A x + Δ x) p v‖ ≤ (Θ * (1 + (κ : ℝ))) * ‖v‖ := by
  have hder : fderiv ℂ (fun x => A x + Δ x) p = fderiv ℂ A p + fderiv ℂ Δ p :=
    (hA.hasFDerivAt.add hΔ.hasFDerivAt).fderiv
  rw [hder]
  change _ ≤ ‖fderiv ℂ A p v + fderiv ℂ Δ p v‖ ∧
    ‖fderiv ℂ A p v + fderiv ℂ Δ p v‖ ≤ _
  have hd := ((fderiv ℂ Δ p).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hdΔ (norm_nonneg v))
  have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθΘ κ.coe_nonneg)
    (norm_nonneg v)
  have hl : ‖fderiv ℂ A p v‖ ≤
      ‖fderiv ℂ A p v + fderiv ℂ Δ p v‖ + ‖fderiv ℂ Δ p v‖ := by
    simpa using norm_sub_le (fderiv ℂ A p v + fderiv ℂ Δ p v) (fderiv ℂ Δ p v)
  constructor
  · nlinarith [hlo v]
  · nlinarith [hhi v, norm_add_le (fderiv ℂ A p v) (fderiv ℂ Δ p v)]

theorem frequencyShiftData_of_old_inverse {n : ℕ}
    {g Δ : ComplexSpace n → ComplexSpace n} {G V : Set (ComplexSpace n)}
    {β κ : ℝ≥0} {θ : ℝ} (hβ : 0 < β) (hκ : κ < 1) (hθ : 0 < θ)
    (hg : AnalyticOnNhd ℂ g V) (hmap : MapsTo g V G)
    (hΔ : AnalyticOnNhd ℂ Δ G) (hb : NormBoundOn Δ G β)
    (hdg : ∀ x ∈ V, ‖fderiv ℂ g x‖ ≤ θ⁻¹)
    (hdΔ : ∀ p ∈ G, ‖fderiv ℂ Δ p‖ ≤ (κ : ℝ) * θ) :
    FrequencyShiftData (Δ ∘ g) V β κ := by
  refine ⟨hβ, hκ, ?_, ⟨β.coe_nonneg, fun x hx => hb.norm_le (hmap hx)⟩, ?_⟩
  · intro x hx
    exact (hΔ _ (hmap hx)).comp (hg x hx)
  · intro x hx
    rw [fderiv_comp x (hΔ _ (hmap hx)).differentiableAt (hg x hx).differentiableAt]
    calc
      _ ≤ ‖fderiv ℂ Δ (g x)‖ * ‖fderiv ℂ g x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ((κ : ℝ) * θ) * θ⁻¹ :=
        mul_le_mul (hdΔ _ (hmap hx)) (hdg x hx) (norm_nonneg _) (by positivity)
      _ = κ := by field_simp

/-- The inverse of a corrected frequency chart, composed with the original inverse chart. -/
def correctedFrequencyInverse {n : ℕ} (g Δ : ComplexSpace n → ComplexSpace n)
    (V : Set (ComplexSpace n)) (β : ℝ≥0) : ComplexSpace n → ComplexSpace n :=
  g ∘ frequencyInverse (Δ ∘ g) V β

theorem correctedFrequencyInverse_analytic {n : ℕ}
    {g Δ : ComplexSpace n → ComplexSpace n} {V : Set (ComplexSpace n)} {β κ : ℝ≥0}
    (d : FrequencyShiftData (Δ ∘ g) V β κ) (hg : AnalyticOnNhd ℂ g V) :
    AnalyticOnNhd ℂ (correctedFrequencyInverse g Δ V β) (frequencyInverseTarget V β) := by
  intro y hy
  exact (hg _ (erosion_subset _ _ (d.inverse_spec hy).1)).comp (d.inverse_analytic_right hy).1

theorem correctedFrequencyInverse_right {n : ℕ}
    {A g Δ : ComplexSpace n → ComplexSpace n} {V : Set (ComplexSpace n)} {β κ : ℝ≥0}
    (d : FrequencyShiftData (Δ ∘ g) V β κ) (hA : ∀ x ∈ V, A (g x) = x)
    {y : ComplexSpace n} (hy : y ∈ frequencyInverseTarget V β) :
    A (correctedFrequencyInverse g Δ V β y) +
      Δ (correctedFrequencyInverse g Δ V β y) = y := by
  dsimp [correctedFrequencyInverse]
  rw [hA _ (erosion_subset _ _ (d.inverse_spec hy).1)]
  exact (d.inverse_spec hy).2.1

theorem correctedFrequencyInverse_injOn {n : ℕ}
    {A g Δ : ComplexSpace n → ComplexSpace n} {V : Set (ComplexSpace n)} {β κ : ℝ≥0}
    (d : FrequencyShiftData (Δ ∘ g) V β κ) (hA : ∀ x ∈ V, A (g x) = x) :
    InjOn (correctedFrequencyInverse g Δ V β) (frequencyInverseTarget V β) := by
  intro x hx y hy he
  rw [← correctedFrequencyInverse_right d hA hx,
    ← correctedFrequencyInverse_right d hA hy, he]

theorem correctedFrequency_image_domain {n : ℕ}
    {A g Δ : ComplexSpace n → ComplexSpace n} {V Ω₁ : Set (ComplexSpace n)} {β κ : ℝ≥0}
    (d : FrequencyShiftData (Δ ∘ g) V β κ) (hA : ∀ x ∈ V, A (g x) = x)
    (hΩ₁ : Ω₁ ⊆ frequencyInverseTarget V β) :
    (fun p => A p + Δ p) '' (correctedFrequencyInverse g Δ V β '' Ω₁) = Ω₁ := by
  rw [image_image]
  ext y
  constructor
  · rintro ⟨x, hx, he⟩
    have hr := correctedFrequencyInverse_right d hA (hΩ₁ hx)
    have hxy : x = y := hr.symm.trans he
    exact hxy ▸ hx
  · intro hy
    exact ⟨y, hy, correctedFrequencyInverse_right d hA (hΩ₁ hy)⟩

end KamProject.Arnold1963
