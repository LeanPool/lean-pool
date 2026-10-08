/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityContinuity

/-!
# Bookkeeping for the chain of interior estimates

Nested boxes, monotonicity of integrals of nonnegative densities in the domain, and integral
bounds from pointwise bounds, used to chain the interior estimates of
`thm:vorticity-regularity`.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Nested boxes with a common top time. -/
theorem vorticityBox_subset (x₀ : Vec3) {r R a b : ℝ} (t₀ : ℝ) (hrR : r ≤ R) (hab : a ≤ b) :
    (vec3Ball x₀ r ×ˢ Ioo b t₀ : Set (Vec3 × ℝ)) ⊆ vec3Ball x₀ R ×ˢ Ioo a t₀ := by
  rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
  exact ⟨vec3Ball_mono hrR hx, lt_of_le_of_lt hab ht1, ht2⟩

/-- The integral of a nonnegative density over a subset is bounded by any bound of the integral
over the larger set. -/
theorem vorticity_setIntegral_le_of_subset {S T : Set (Vec3 × ℝ)} (hST : S ⊆ T)
    {g : Vec3 × ℝ → ℝ} (hg : IntegrableOn g T) (h0 : ∀ z, 0 ≤ g z) {K : ℝ}
    (hK : ∫ z in T, g z ≤ K) : ∫ z in S, g z ≤ K :=
  (setIntegral_mono_set hg (Eventually.of_forall fun z => h0 z) hST.eventuallyLE).trans hK

/-- An integral bound from a pointwise bound by a combination of two integrable densities. -/
theorem vorticity_integral_le_combo {μ : Measure (Vec3 × ℝ)} {f g₁ g₂ : Vec3 × ℝ → ℝ}
    {c₁ c₂ K₁ K₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hf0 : ∀ z, 0 ≤ f z)
    (hg₁ : Integrable g₁ μ) (hg₂ : Integrable g₂ μ)
    (hle : ∀ᵐ z ∂μ, f z ≤ c₁ * g₁ z + c₂ * g₂ z)
    (h₁ : ∫ z, g₁ z ∂μ ≤ K₁) (h₂ : ∫ z, g₂ z ∂μ ≤ K₂) :
    ∫ z, f z ∂μ ≤ c₁ * K₁ + c₂ * K₂ := by
  have hi : Integrable (fun z => c₁ * g₁ z + c₂ * g₂ z) μ :=
    (hg₁.const_mul c₁).add (hg₂.const_mul c₂)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun z => hf0 z) hi hle).trans ?_
  rw [integral_add (hg₁.const_mul c₁) (hg₂.const_mul c₂), integral_const_mul, integral_const_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left h₁ hc₁) (mul_le_mul_of_nonneg_left h₂ hc₂)

/-- One square of a matrix is bounded by the sum of all its squares. -/
theorem vorticity_sq_le_sum_two (f : Fin 3 → Fin 3 → ℝ) (a b : Fin 3) :
    f a b ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, f i j ^ 2 :=
  (Finset.single_le_sum (f := fun j => f a j ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun i => ∑ j : Fin 3, f i j ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a))

/-- One square of a three-index array is bounded by the sum of all its squares. -/
theorem vorticity_sq_le_sum_three (f : Fin 3 → Fin 3 → Fin 3 → ℝ) (a b c : Fin 3) :
    f a b c ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f i j k ^ 2 :=
  (vorticity_sq_le_sum_two (f a) b c).trans
    (Finset.single_le_sum (f := fun i => ∑ j : Fin 3, ∑ k : Fin 3, f i j k ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_univ a))

end ESS
