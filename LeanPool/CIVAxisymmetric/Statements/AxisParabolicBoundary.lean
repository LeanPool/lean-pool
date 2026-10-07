/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Basic.Real.Basic

/-!
# Axis Parabolic Boundary

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section


noncomputable section

namespace CIV

/-- The parabolic boundary `Σ` of `lem:aniso:axis`: the initial slice and the lateral
half-circle. -/
@[expose] def axisParabolicBoundary (R t₁ s : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | 0 ≤ p.1.1 ∧ p.1.1 ^ 2 + p.1.2 ^ 2 ≤ R ^ 2 ∧ p.2 = t₁} ∪
    {p | 0 ≤ p.1.1 ∧ p.1.1 ^ 2 + p.1.2 ^ 2 = R ^ 2 ∧ t₁ ≤ p.2 ∧ p.2 ≤ s}

end CIV
