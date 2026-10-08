/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Force Spatially Analytic

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Spatial real analyticity of the force, locally uniformly on cylinders compactly contained
in `Q`, `eq:interior:force:analytic`. -/
@[expose] def ForceSpatiallyAnalytic (f : ParabolicPoint → Vec3) : Prop :=
  ∀ R : ℝ, R < 1 → ∀ t₁ t₂ : ℝ, -1 < t₁ → t₂ < 0 →
    ∃ M a : ℝ, 0 < a ∧ ∀ α : Fin 3 → ℕ, ∀ t ∈ Icc t₁ t₂, ∀ x ∈ vec3Ball 0 R, ∀ i : Fin 3,
      |multiPartial (fun w => f w i) α (x, t)| ≤
        M * a ^ (-((α 0 + α 1 + α 2 : ℕ) : ℝ)) * Nat.factorial (α 0 + α 1 + α 2)

end CIV
