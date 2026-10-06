/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ThetaTransportDivergenceForm

/-!
# Receding Dt Past Pairing Assembly

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- Assembling the five term-pairing bounds (transport/divergence, diffusion, curvature,
swirl, force — each independently established) via `zoomTheta_pde_divergenceForm` into a
single domination bound on `∫ (dtPast Θ_n)(·, τ) ψ`, the time-pairing estimate
`hpair` of the receding compactness. This is the "pointwise-in-`τ` derivative bound coming from the zoom PDE" that
`CIV.hasDerivAt_integral_mul_testfunction_of_dominated` differentiates under the integral
sign, and that `CIV.abs_sub_le_of_forall_hasDerivAt_le` then turns into the literal `hpair`
shape. Each of the five pieces is continuous with compact support (`tsupport ψ`), hence
integrable; that fact is carried explicitly since the five term-pairing lemmas are proved
separately. -/
theorem dtPast_zoomTheta_pairing_bound_fixed {h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {K : Set (ℝ × ℝ)} {τ : ℝ}
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (hApos : ∀ y ∈ K, (1 : ℝ) ≤ rc / lam + y.1)
    (ψ : ℝ × ℝ → ℝ) (hψU : tsupport ψ ⊆ interior K) (B : ℝ)
    -- the five term-pairing bounds, each independently established (carried here by their
    -- exact concluding shape, since their own target files are proved separately)
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

/-- The existential form of `dtPast_zoomTheta_pairing_bound_fixed`, bundling its five explicit
constants into the single `∃ C₀, 0 ≤ C₀ ∧ ...` shape the domination hypothesis `hdom` of
`CIV.exists_time_pairing_bound_of_dtPast_bound_zoomTheta`
(`CIV/Zoom/RecedingTimePairingWiring.lean`)
needs at a fixed `τ`. -/
theorem exists_dtPast_zoomTheta_pairing_bound_fixed {h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {K : Set (ℝ × ℝ)} {τ : ℝ}
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (hApos : ∀ y ∈ K, (1 : ℝ) ≤ rc / lam + y.1)
    (ψ : ℝ × ℝ → ℝ) (hψU : tsupport ψ ⊆ interior K) (B : ℝ)
    (C_transport C_diffusion C_curvature C_swirl C_force : ℝ)
    (hC_transport : 0 ≤ C_transport) (hC_diffusion : 0 ≤ C_diffusion)
    (hC_curvature : 0 ≤ C_curvature) (hC_swirl : 0 ≤ C_swirl) (hC_force : 0 ≤ C_force)
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
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      |∫ y : ℝ × ℝ, dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ) * ψ y|
        ≤ C₀ * B :=
  ⟨C_transport + C_diffusion + C_curvature + C_swirl + C_force,
    by linarith only [hC_transport, hC_diffusion, hC_curvature, hC_swirl, hC_force],
    dtPast_zoomTheta_pairing_bound_fixed hlam hsol haxi hmem hApos ψ hψU B C_transport
      C_diffusion C_curvature C_swirl C_force T1 T2 T3 T4 T5 hT1_def hT2_def hT3_def hT4_def
      hT5_def hint1 hint2 hint3 hint4 hint5 hbound1 hbound2 hbound3 hbound4 hbound5⟩

/-- The eventual-in-`n` domination bound: for a sequence of zoom scales, once the pointwise
divergence-form identity, the membership/offset side conditions and the five term-pairing
bounds all hold eventually, the same domination bound on `∫ (dtPast Θ_n)(·, τ) ψ` holds
eventually, with `C₀` chosen before `n`, matching the eventual form of
`hpair`'s underlying derivative bound. -/
theorem dtPast_zoomTheta_pairing_bound {h rc zc : ℝ} (lam : ℕ → ℝ) (hlam_pos : ∀ n, 0 < lam n)
    {u : ParabolicPoint → Vec3} {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {K : Set (ℝ × ℝ)} (_ : IsCompact K) {τ : ℝ}
    (hmem : ∀ᶠ n in atTop, ∀ y ∈ K, zoomPointRec (lam n) h rc zc (y, τ) ∈ unitCylinder)
    (hApos : ∀ᶠ n in atTop, ∀ y ∈ K, (1 : ℝ) ≤ rc / lam n + y.1)
    (ψ : ℝ × ℝ → ℝ) (_ : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ interior K) (B : ℝ)
    (C_transport C_diffusion C_curvature C_swirl C_force : ℝ)
    (T1 T2 T3 T4 T5 : ℕ → ℝ × ℝ → ℝ)
    (hT1_def : ∀ n, T1 n = fun y => -(dr (fun q : (ℝ × ℝ) × ℝ =>
        zoomVRec (lam n) h rc zc u q * zoomTheta (lam n) h rc zc u q) (y, τ)
      + dz (fun q : (ℝ × ℝ) × ℝ =>
        zoomWRec (lam n) h rc zc u q * zoomTheta (lam n) h rc zc u q) (y, τ)))
    (hT2_def : ∀ n, T2 n = fun y =>
      dr (dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h rc zc u q)) (y, τ)
      + (lam n ^ (2 * h)) ^ 2 *
        dz (dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h rc zc u q)) (y, τ))
    (hT3_def : ∀ n, T3 n = fun y =>
      dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h rc zc u q) (y, τ) / (rc / lam n + y.1)
        - zoomTheta (lam n) h rc zc u (y, τ) / (rc / lam n + y.1) ^ 2)
    (hT4_def : ∀ n, T4 n = fun y => 1 / (rc / lam n + y.1) *
      dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec (lam n) h rc zc u q ^ 2) (y, τ))
    (hT5_def : ∀ n, T5 n = fun y =>
      lam n ^ 4 * lam n ^ (2 * h) * curlComp f 1 (zoomPointRec (lam n) h rc zc (y, τ)))
    (hint : ∀ᶠ n in atTop, Integrable (fun y => T1 n y * ψ y) ∧ Integrable (fun y => T2 n y * ψ y)
      ∧ Integrable (fun y => T3 n y * ψ y) ∧ Integrable (fun y => T4 n y * ψ y)
      ∧ Integrable (fun y => T5 n y * ψ y))
    (hbound : ∀ᶠ n in atTop,
      |∫ y : ℝ × ℝ, T1 n y * ψ y| ≤ C_transport * B ∧
      |∫ y : ℝ × ℝ, T2 n y * ψ y| ≤ C_diffusion * B ∧
      |∫ y : ℝ × ℝ, T3 n y * ψ y| ≤ C_curvature * B ∧
      |∫ y : ℝ × ℝ, T4 n y * ψ y| ≤ C_swirl * B ∧
      |∫ y : ℝ × ℝ, T5 n y * ψ y| ≤ C_force * B) :
    ∀ᶠ n in atTop,
      |∫ y : ℝ × ℝ, dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h rc zc u q) (y, τ) * ψ y|
        ≤ (C_transport + C_diffusion + C_curvature + C_swirl + C_force) * B := by
  filter_upwards [hmem, hApos, hint, hbound] with n hmem_n hApos_n hint_n hbound_n
  obtain ⟨hi1, hi2, hi3, hi4, hi5⟩ := hint_n
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hbound_n
  exact dtPast_zoomTheta_pairing_bound_fixed (hlam_pos n) hsol haxi hmem_n hApos_n ψ hψU
    B
    C_transport C_diffusion C_curvature C_swirl C_force (T1 n) (T2 n) (T3 n) (T4 n) (T5 n)
    (hT1_def n) (hT2_def n) (hT3_def n) (hT4_def n) (hT5_def n) hi1 hi2 hi3 hi4 hi5 hb1 hb2 hb3
    hb4 hb5

end CIV
