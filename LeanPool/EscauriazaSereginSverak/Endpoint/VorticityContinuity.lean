/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityFinalBound
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityContinuityExport

/-!
# The continuous representative of the vorticity

A field solving a heat equation with square-integrable flux, whose first and second spatial
weak derivatives solve heat equations of the same kind, has a representative which is continuous
and bounded up to the top time on a smaller closed box: at every time the backward mollifications
are Cauchy in the uniform norm, by the `H²` embedding and the uniform-in-time `L²` Cauchy property
of the mollified fields (the continuity statement of `thm:vorticity-regularity`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A continuous bounded representative on the closed box, from heat equations for the field and
its first and second spatial weak derivatives. -/
theorem vorticity_continuousRep (Kw K1 K2 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (a t₀ : ℝ) (w : Vec3 × ℝ → ℝ)
      (g Fw : Fin 3 → Vec3 × ℝ → ℝ) (h Fg : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
      (Fh : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
    a + 1 / 64 < t₀ → t₀ ≤ a + 1 →
    MemLp w 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀)) →
    (∀ m, MemLp (g m) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ m k, MemLp (h m k) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ j, MemLp (Fw j) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ m j, MemLp (Fg m j) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ m k j, MemLp (Fh m k j) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, w y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, g j y * ψ y) →
    (∀ m k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, g m y * spatialPartial ψ k y =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, h m k y * ψ y) →
    (∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, ∑ j : Fin 3, Fw j y * spatialPartial ψ j y) →
    (∀ m : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          g m y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          ∑ j : Fin 3, Fg m j y * spatialPartial ψ j y) →
    (∀ m k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          h m k y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          ∑ j : Fin 3, Fh m k j y * spatialPartial ψ j y) →
    (∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, (w y ^ 2 + ∑ j : Fin 3, Fw j y ^ 2)) ≤ Kw →
    (∀ m, ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
      (g m y ^ 2 + ∑ j : Fin 3, Fg m j y ^ 2) ≤ K1) →
    (∀ m k, ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
      (h m k y ^ 2 + ∑ j : Fin 3, Fh m k j y ^ 2) ≤ K2) →
    ∃ ω : Vec3 × ℝ → ℝ,
      ContinuousOn ω ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ Icc (a + 1 / 64) t₀) ∧
      (∀ z ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ Icc (a + 1 / 64) t₀ :
        Set (Vec3 × ℝ)), |ω z| ≤ C) ∧
      ω =ᵐ[volume.restrict (vec3Ball x₀ (38 / 64) ×ˢ Ioo (a + 1 / 64) t₀)] w := by
  obtain ⟨C, _, hC, _, hproperty⟩ :=
    vorticity_continuousRep_export Kw K1 K2
  refine ⟨C, hC, ?_⟩
  intro x₀ a t₀ w g Fw h Fg Fh hat hta hw hg hh hFw hFg hFh hdw hdg hheatw hheatg hheath
    hKw hK1 hK2
  obtain ⟨_, _, ω, hcontinuous, hbounded, hae, _, _⟩ :=
    hproperty x₀ a t₀ w g Fw h Fg Fh hat hta hw hg hh hFw hFg hFh hdw hdg hheatw hheatg hheath
      hKw hK1 hK2
  exact ⟨ω, hcontinuous, hbounded, hae⟩

end ESS
