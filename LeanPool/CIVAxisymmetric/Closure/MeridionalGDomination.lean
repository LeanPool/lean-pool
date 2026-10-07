/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.MeridionalG

/-!
`meridionalQuantity ≤ meridionalG` and `meridionalG_nonneg` (the nonnegativity of the
supremum `G_ρ(t)`), together with the bundled existence theorem that collects all three
consequences of `MeridionalSmallness` in one call.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem meridionalG_nonneg {ρ : ℝ} {u : ParabolicPoint → Vec3} {t : ℝ}
    (hne : ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball 0 ρ) :
    0 ≤ meridionalG ρ u t := by
  obtain ⟨x₁, x₃, hmem⟩ := hne
  by_cases hbdd : BddAbove {q : ℝ | ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball 0 ρ ∧
    q = meridionalQuantity u (meridional x₁ x₃, t)}
  · have hpos : 0 ≤ meridionalQuantity u (meridional x₁ x₃, t) := by
      unfold meridionalQuantity
      positivity
    have hle : meridionalQuantity u (meridional x₁ x₃, t) ≤
        sSup {q : ℝ | ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball 0 ρ ∧
          q = meridionalQuantity u (meridional x₁ x₃, t)} :=
      le_csSup hbdd ⟨x₁, x₃, hmem, rfl⟩
    unfold meridionalG
    linarith only [hpos, hle]
  · unfold meridionalG
    rw [Real.sSup_of_not_bddAbove hbdd]

theorem meridionalQuantity_le_meridionalG {ρ : ℝ} {u : ParabolicPoint → Vec3} {t : ℝ}
    (hbdd : BddAbove {q : ℝ | ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball 0 ρ ∧
      q = meridionalQuantity u (meridional x₁ x₃, t)})
    {x₁ x₃ : ℝ} (hmem : meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ) :
    meridionalQuantity u (meridional x₁ x₃, t) ≤ meridionalG ρ u t := by
  unfold meridionalG
  exact le_csSup hbdd ⟨x₁, x₃, hmem, rfl⟩

theorem exists_meridionalG_hG_of_meridionalSmallness {ρ η : ℝ} (hη : 0 < η)
    {u : ParabolicPoint → Vec3} (hsmall : MeridionalSmallness ρ u)
    (hbdd : ∀ t : ℝ, BddAbove {q : ℝ | ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball 0 ρ ∧
      q = meridionalQuantity u (meridional x₁ x₃, t)})
    (hne : ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball 0 ρ) :
    ∃ tη ∈ Ioo (-1 : ℝ) 0,
      (∀ t ∈ Ioo tη 0, 0 ≤ meridionalG ρ u t) ∧
      (∀ t ∈ Ioo tη 0, ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        meridionalQuantity u (meridional x₁ x₃, t) ≤ meridionalG ρ u t) ∧
      (∀ t ∈ Ioo tη 0, meridionalG ρ u t ≤ η / (-t)) := by
  obtain ⟨tη, htη, hdecay⟩ := meridionalG_le_of_meridionalSmallness hη hsmall hne
  refine ⟨tη, htη, ?_, ?_, hdecay⟩
  · exact fun t _ => meridionalG_nonneg hne
  · exact fun t _ x₁ x₃ hmem => meridionalQuantity_le_meridionalG (hbdd t) hmem

end CIV
