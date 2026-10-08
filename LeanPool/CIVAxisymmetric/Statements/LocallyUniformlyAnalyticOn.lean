/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AnalyticBoundOn

/-!
# Locally Uniformly Analytic On

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Spatial analyticity of a field, locally uniformly on cylinders compactly contained in
`B(R) × (t₁, t₂)`: `eq:analytic:interior:force` / `eq:analytic:interior:velocity`. -/
@[expose] def LocallyUniformlyAnalyticOn (g : ParabolicPoint → Vec3) (R t₁ t₂ : ℝ) : Prop :=
  ∀ R' : ℝ, R' < R → ∀ s₁ s₂ : ℝ, t₁ < s₁ → s₂ < t₂ →
    ∃ M a : ℝ, 0 < a ∧ AnalyticBoundOn g R' (Icc s₁ s₂) M a

end CIV
