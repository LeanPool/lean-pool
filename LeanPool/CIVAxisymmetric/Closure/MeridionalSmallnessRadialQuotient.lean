/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MeridionalSmallness
public import LeanPool.CIVAxisymmetric.Statements.MeridionalQuantity

/-!
The reduction of `MeridionalSmallness` (`eq:aniso:small`, the conclusion of
`prop:aniso:small`) to the single-term bound on `u_r / r` that the swirl equation's maximum
principle (`eq:aniso:closure:w`) consumes as its smallness hypothesis, the pointwise domination
`radialQuotient` and the other components of `eq:aniso:G` by their sum being the only step needed.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV



theorem abs_radialQuotient_le_meridionalQuantity (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    |radialQuotient u z| ≤ meridionalQuantity u z := by
  unfold meridionalQuantity
  have h0 : 0 ≤ |CKN.spatialPartial (fun w => u w 0) 0 z| := abs_nonneg _
  have h2 : 0 ≤ |CKN.spatialPartial (fun w => u w 2) 2 z| := abs_nonneg _
  have h3 : 0 ≤ |CKN.spatialPartial (fun w => u w 0) 2 z| := abs_nonneg _
  linarith only [h0, h2, h3]

theorem abs_spatialPartial_radial_le_meridionalQuantity (u : ParabolicPoint → Vec3)
    (z : ParabolicPoint) :
    |CKN.spatialPartial (fun w => u w 0) 0 z| ≤ meridionalQuantity u z := by
  unfold meridionalQuantity
  have h0 : 0 ≤ |radialQuotient u z| := abs_nonneg _
  have h2 : 0 ≤ |CKN.spatialPartial (fun w => u w 2) 2 z| := abs_nonneg _
  have h3 : 0 ≤ |CKN.spatialPartial (fun w => u w 0) 2 z| := abs_nonneg _
  linarith only [h0, h2, h3]

theorem abs_spatialPartial_axial_le_meridionalQuantity (u : ParabolicPoint → Vec3)
    (z : ParabolicPoint) :
    |CKN.spatialPartial (fun w => u w 2) 2 z| ≤ meridionalQuantity u z := by
  unfold meridionalQuantity
  have h0 : 0 ≤ |CKN.spatialPartial (fun w => u w 0) 0 z| := abs_nonneg _
  have h1 : 0 ≤ |radialQuotient u z| := abs_nonneg _
  have h3 : 0 ≤ |CKN.spatialPartial (fun w => u w 0) 2 z| := abs_nonneg _
  linarith only [h0, h1, h3]

theorem tendsto_radialQuotient_of_meridionalSmallness {ρ : ℝ} {u : ParabolicPoint → Vec3}
    (hsmall : MeridionalSmallness ρ u) :
    ∀ ε : ℝ, 0 < ε → ∃ t₀ ∈ Ioo (-1 : ℝ) 0, ∀ t ∈ Ioo t₀ 0, ∀ x₁ x₃ : ℝ,
      meridional x₁ x₃ ∈ vec3Ball 0 ρ → (-t) * |radialQuotient u (meridional x₁ x₃, t)| ≤ ε := by
  intro ε hε
  rcases hsmall ε hε with ⟨t₀, ht₀, hbound⟩
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht x₁ x₃ hmem
  have hneg : 0 ≤ -t := by
    have : t < 0 := ht.2
    linarith only [this]
  have hineq1 : (-t) * |radialQuotient u (meridional x₁ x₃, t)| ≤
      (-t) * meridionalQuantity u (meridional x₁ x₃, t) := by
    gcongr
    exact abs_radialQuotient_le_meridionalQuantity u (meridional x₁ x₃, t)
  have hineq2 : (-t) * meridionalQuantity u (meridional x₁ x₃, t) ≤ ε :=
    hbound t ht x₁ x₃ hmem
  linarith only [hineq1, hineq2]

theorem swirl_hG_of_meridionalSmallness {ρ Rstar η : ℝ} {u : ParabolicPoint → Vec3}
    (hsmall : MeridionalSmallness ρ u) (hη : 0 < η) (hRstar : Rstar ≤ ρ) :
    ∃ tη ∈ Ioo (-1 : ℝ) 0, ∀ t ∈ Ioo tη (0 : ℝ), ∀ x₁ x₃ : ℝ,
      meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t) := by
  rcases tendsto_radialQuotient_of_meridionalSmallness hsmall η hη with ⟨tη, htη, hbound⟩
  refine ⟨tη, htη, ?_⟩
  intro t ht x₁ x₃ hmem
  have hmem' : meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ :=
    vec3Ball_mono hRstar hmem
  have h := hbound t ht x₁ x₃ hmem'
  have hpos : 0 < -t := by
    have : t < 0 := ht.2
    linarith only [this]
  rw [le_div_iff₀ hpos]
  calc
    |radialQuotient u (meridional x₁ x₃, t)| * (-t) = (-t) * |radialQuotient u (meridional x₁
      x₃, t)| := by
      ring
    _ ≤ η := h

end CIV
