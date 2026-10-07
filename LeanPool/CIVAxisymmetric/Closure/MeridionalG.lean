/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MeridionalSmallness

/-!
# Meridional G

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The supremum `G_ρ(t)` of `eq:aniso:G`, over the meridional-plane points of `B(ρ)`. -/
@[expose] def meridionalG (ρ : ℝ) (u : ParabolicPoint → Vec3) (t : ℝ) : ℝ :=
  sSup {q : ℝ | ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball 0 ρ ∧
    q = meridionalQuantity u (meridional x₁ x₃, t)}

/-- The reduction of `MeridionalSmallness` (`eq:aniso:small`) to the pointwise decay
`G_ρ(t) ≤ η/(-t)` that `lem:aniso:closure`'s Grönwall step consumes.

No boundedness of the meridional quantity set is needed: the bound is proved by `csSup_le`,
which needs only that the set is nonempty and that every element is at most `η/(-t)`. -/
theorem meridionalG_le_of_meridionalSmallness {ρ η : ℝ} (hη : 0 < η) {u : ParabolicPoint → Vec3}
    (hsmall : MeridionalSmallness ρ u)
    (hne : ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball 0 ρ) :
    ∃ tη ∈ Ioo (-1 : ℝ) 0, ∀ t ∈ Ioo tη 0, meridionalG ρ u t ≤ η / (-t) := by
  obtain ⟨tη, htη, hbound⟩ := hsmall η hη
  refine ⟨tη, htη, fun t ht => ?_⟩
  have hnegt : (0 : ℝ) < -t := neg_pos.mpr ht.2
  have hne' : Set.Nonempty {q : ℝ | ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball 0 ρ ∧
      q = meridionalQuantity u (meridional x₁ x₃, t)} := by
    obtain ⟨x1, x3, hmem⟩ := hne
    exact ⟨meridionalQuantity u (meridional x1 x3, t), x1, x3, hmem, rfl⟩
  refine csSup_le hne' ?_
  rintro q ⟨x1, x3, hmem, rfl⟩
  rw [le_div_iff₀ hnegt]
  simpa [mul_comm] using hbound t ht x1 x3 hmem

end CIV
