/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.Meridional
public import LeanPool.CIVAxisymmetric.Statements.MeridionalQuantity

/-!
# Meridional Smallness

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- `lim_{t↑0} (-t) G_ρ(t) = 0`, `eq:aniso:small`, unfolded. -/
@[expose] def MeridionalSmallness (ρ : ℝ) (u : ParabolicPoint → Vec3) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ t₀ ∈ Ioo (-1 : ℝ) 0, ∀ t ∈ Ioo t₀ 0, ∀ x₁ x₃ : ℝ,
    meridional x₁ x₃ ∈ vec3Ball 0 ρ → (-t) * meridionalQuantity u (meridional x₁ x₃, t) ≤ ε

end CIV
