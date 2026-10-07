/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Dr

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section


noncomputable section

namespace CIV

/-- `∂_r` of a function of `((r, z), t)`. -/
@[expose] def dr (φ : (ℝ × ℝ) × ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  deriv (fun r => φ ((r, p.1.2), p.2)) p.1.1

end CIV
