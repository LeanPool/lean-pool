/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Dt Past

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section


noncomputable section

namespace CIV

/-- The one-sided (from the past) time derivative of a function of `((r, z), t)`. -/
@[expose] def dtPast (φ : (ℝ × ℝ) × ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  derivWithin (fun t => φ (p.1, t)) (Set.Iic p.2) p.2

end CIV
