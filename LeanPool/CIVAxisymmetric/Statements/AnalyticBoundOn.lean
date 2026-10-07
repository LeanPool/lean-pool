/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Analytic Bound On

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The analyticity bound `eq:analytic:interior:force` for a field `g` on `B(R') × J`
with constants `M`, `a`. -/
@[expose] def AnalyticBoundOn (g : ParabolicPoint → Vec3) (R' : ℝ) (J : Set ℝ) (M a : ℝ) : Prop :=
  ∀ α : Fin 3 → ℕ, ∀ t ∈ J, ∀ x ∈ vec3Ball 0 R', ∀ i : Fin 3,
    |multiPartial (fun w => g w i) α (x, t)| ≤
      M * a ^ (-((α 0 + α 1 + α 2 : ℕ) : ℝ)) * Nat.factorial (α 0 + α 1 + α 2)

end CIV
