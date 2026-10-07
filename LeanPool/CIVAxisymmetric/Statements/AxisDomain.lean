/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Basic.Real.Basic

/-!
# Axis Domain

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section


noncomputable section

namespace CIV

/-- The half-disc `{r > 0, r² + z² < R²}` with the times `(t₁, s]`: the set `D` of
`lem:aniso:axis`. -/
@[expose] def axisDomain (R t₁ s : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | 0 < p.1.1 ∧ p.1.1 ^ 2 + p.1.2 ^ 2 < R ^ 2 ∧ t₁ < p.2 ∧ p.2 ≤ s}

end CIV
