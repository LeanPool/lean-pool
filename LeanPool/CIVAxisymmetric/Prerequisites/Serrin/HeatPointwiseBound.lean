/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatCutoffDecomposition
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatPointwiseAssembly

/-!
# The pointwise heat bound of the interior estimates

`serrin_heat_pointwise_bound` is the final assembly of the cut-off heat representation: it
chains `HB2_cutoff_decomposition` into `heat_pointwise_bound_of_decomposition` to give
`|w (x, s)| ≤ C (ρ Λ + M / ρ)` from the hypotheses that `w = div U` and `(∂ₜ − Δ) w = div Y` on
an open set containing the backward parabolic window, with `Y` bounded by `Λ` and `U` bounded by
`M` on the window. This is the pointwise heat bound of the interior estimates in the proof of
`lem:aniso:annulus`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

noncomputable section
namespace CIV



theorem serrin_heat_pointwise_bound : ∃ C : ℝ, 0 < C ∧ ∀ (w : ParabolicPoint → ℝ)
    (U Y : Fin 3 → ParabolicPoint → ℝ) (O : Set ParabolicPoint) (x : Vec3) (s ρ Λ M : ℝ),
    IsOpen (X := Vec3 × ℝ) O → 0 < ρ → ρ ≤ 1 →
    {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s ⊆ O →
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => w z) O →
    (∀ l, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => U l z) O) →
    (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => Y j z) O) →
    (∀ z ∈ O, w z = ∑ l, spatialPartial (U l) l z) →
    (∀ z ∈ O, timePartial w z - ∑ j, spatialSecondPartial w j j z =
      ∑ j, spatialPartial (Y j) j z) →
    (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s, ∀ j, |Y j z| ≤ Λ) →
    (∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s, ∀ l, |U l z| ≤ M) →
    |w (x, s)| ≤ C * (ρ * Λ + M / ρ) := by
  obtain ⟨C, hC, hCb⟩ := heat_pointwise_bound_of_decomposition
  refine ⟨C, hC, ?_⟩
  intro w U Y O x s ρ Λ M hO hρ hρ1 hwin hw hU hY hwU heq hYb hUb
  exact hCb w U Y x s ρ Λ M hρ hρ1 hYb hUb
    (HB2_cutoff_decomposition hO hρ hρ1 hwin hw hU hY hwU heq)

end CIV
