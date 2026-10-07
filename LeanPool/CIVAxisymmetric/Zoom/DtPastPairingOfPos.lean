/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ThetaTransportDivergenceForm

/-!
# The pairing of `∂_τ Θ_n` against a test function, off the recentred axis

The assembly `CIV.dtPast_zoomTheta_pairing_bound_fixed` of `CIV.Zoom.RecedingDtPastPairingAssembly`
with the offset `A + R` of `eq:aniso:zoom:receding:equation` only required to be positive on
the support; the assembly uses it only to stay off the recentred axis.
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The five term pairings of `eq:aniso:zoom:receding:equation` (transport in divergence form,
diffusion, curvature, swirl source, force), each bounded against a test function `ψ`, bound
the pairing of `∂_τ Θ_n` with `ψ`, through the divergence form `zoomTheta_pde_divergenceForm`
of the equation at every point of the support. -/
theorem dtPast_zoomTheta_pairing_bound_fixed_of_pos {h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {K : Set (ℝ × ℝ)} {τ : ℝ}
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (hApos : ∀ y ∈ K, (0 : ℝ) < rc / lam + y.1)
    (ψ : ℝ × ℝ → ℝ) (hψU : tsupport ψ ⊆ interior K) (B : ℝ)
    (C_transport C_diffusion C_curvature C_swirl C_force : ℝ)
    (T1 T2 T3 T4 T5 : ℝ × ℝ → ℝ)
    (hT1_def : T1 = fun y => -(dr (fun q : (ℝ × ℝ) × ℝ =>
        zoomVRec lam h rc zc u q * zoomTheta lam h rc zc u q) (y, τ)
      + dz (fun q : (ℝ × ℝ) × ℝ =>
        zoomWRec lam h rc zc u q * zoomTheta lam h rc zc u q) (y, τ)))
    (hT2_def : T2 = fun y => dr (dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ)
      + (lam ^ (2 * h)) ^ 2 *
        dz (dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ))
    (hT3_def : T3 = fun y =>
      dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ) / (rc / lam + y.1)
        - zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) ^ 2)
    (hT4_def : T4 = fun y => 1 / (rc / lam + y.1) *
      dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ))
    (hT5_def : T5 = fun y =>
      lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc (y, τ)))
    (hint1 : Integrable (fun y => T1 y * ψ y)) (hint2 : Integrable (fun y => T2 y * ψ y))
    (hint3 : Integrable (fun y => T3 y * ψ y)) (hint4 : Integrable (fun y => T4 y * ψ y))
    (hint5 : Integrable (fun y => T5 y * ψ y))
    (hbound1 : |∫ y : ℝ × ℝ, T1 y * ψ y| ≤ C_transport * B)
    (hbound2 : |∫ y : ℝ × ℝ, T2 y * ψ y| ≤ C_diffusion * B)
    (hbound3 : |∫ y : ℝ × ℝ, T3 y * ψ y| ≤ C_curvature * B)
    (hbound4 : |∫ y : ℝ × ℝ, T4 y * ψ y| ≤ C_swirl * B)
    (hbound5 : |∫ y : ℝ × ℝ, T5 y * ψ y| ≤ C_force * B) :
    |∫ y : ℝ × ℝ, dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ) * ψ y|
      ≤ (C_transport + C_diffusion + C_curvature + C_swirl + C_force) * B := by
  have hpointwise : ∀ y ∈ K,
      dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ)
        = T1 y + T2 y + T3 y + T4 y + T5 y := by
    intro y hy
    have hR : y.1 ≠ -(rc / lam) := by
      have hApos' := hApos y hy
      intro hcontra
      rw [hcontra] at hApos'
      norm_num at hApos'
    have hpde := zoomTheta_pde_divergenceForm lam h rc zc hlam u pr f hsol haxi (y, τ) (hmem y hy)
      hR
    have hfix : (y, τ).1.1 = y.1 := rfl
    rw [hfix] at hpde
    rw [hT1_def, hT2_def, hT3_def, hT4_def, hT5_def]
    simp only
    linear_combination hpde
  have hintegrand_eq : ∀ y : ℝ × ℝ,
      dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ) * ψ y
        = T1 y * ψ y + T2 y * ψ y + T3 y * ψ y + T4 y * ψ y + T5 y * ψ y := by
    intro y
    by_cases hyK : y ∈ K
    · rw [hpointwise y hyK]; ring
    · have hynotsupp : y ∉ tsupport ψ := fun hcontra => hyK (interior_subset (hψU hcontra))
      rw [image_eq_zero_of_notMem_tsupport hynotsupp]; ring
  have hint_eq : (∫ y : ℝ × ℝ,
      dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ) * ψ y)
      = ∫ y : ℝ × ℝ,
        T1 y * ψ y + T2 y * ψ y + T3 y * ψ y + T4 y * ψ y + T5 y * ψ y :=
    integral_congr_ae (Filter.Eventually.of_forall hintegrand_eq)
  rw [hint_eq]
  have hint12 : Integrable (fun y : ℝ × ℝ => T1 y * ψ y + T2 y * ψ y) := hint1.add hint2
  have hint123 : Integrable (fun y : ℝ × ℝ => T1 y * ψ y + T2 y * ψ y + T3 y * ψ y) :=
    hint12.add hint3
  have hint1234 : Integrable
      (fun y : ℝ × ℝ => T1 y * ψ y + T2 y * ψ y + T3 y * ψ y + T4 y * ψ y) :=
    hint123.add hint4
  rw [integral_add hint1234 hint5, integral_add hint123 hint4, integral_add hint12 hint3,
    integral_add hint1 hint2]
  calc |((((∫ y : ℝ × ℝ, T1 y * ψ y) + ∫ y : ℝ × ℝ, T2 y * ψ y)
          + ∫ y : ℝ × ℝ, T3 y * ψ y) + ∫ y : ℝ × ℝ, T4 y * ψ y) + ∫ y : ℝ × ℝ, T5 y * ψ y|
      ≤ |∫ y : ℝ × ℝ, T1 y * ψ y| + |∫ y : ℝ × ℝ, T2 y * ψ y| + |∫ y : ℝ × ℝ, T3 y * ψ y|
          + |∫ y : ℝ × ℝ, T4 y * ψ y| + |∫ y : ℝ × ℝ, T5 y * ψ y| := by
        have h1 := abs_add_le ((∫ y : ℝ × ℝ, T1 y * ψ y) + ∫ y : ℝ × ℝ, T2 y * ψ y)
          (∫ y : ℝ × ℝ, T3 y * ψ y)
        have h2 := abs_add_le (∫ y : ℝ × ℝ, T1 y * ψ y) (∫ y : ℝ × ℝ, T2 y * ψ y)
        have h3 := abs_add_le
          (((∫ y : ℝ × ℝ, T1 y * ψ y) + ∫ y : ℝ × ℝ, T2 y * ψ y) + ∫ y : ℝ × ℝ, T3 y * ψ y)
          (∫ y : ℝ × ℝ, T4 y * ψ y)
        have h4 := abs_add_le
          ((((∫ y : ℝ × ℝ, T1 y * ψ y) + ∫ y : ℝ × ℝ, T2 y * ψ y) + ∫ y : ℝ × ℝ, T3 y * ψ y)
            + ∫ y : ℝ × ℝ, T4 y * ψ y)
          (∫ y : ℝ × ℝ, T5 y * ψ y)
        linarith only [h1, h2, h3, h4]
    _ ≤ C_transport * B + C_diffusion * B + C_curvature * B + C_swirl * B + C_force * B := by
        linarith only [hbound1, hbound2, hbound3, hbound4, hbound5]
    _ = (C_transport + C_diffusion + C_curvature + C_swirl + C_force) * B := by ring

end CIV
