/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Time Deriv

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN


noncomputable section

namespace CIV

/-- The time derivative of a test function on `Vec m × ℝ`. -/
@[expose] def timeDeriv (m : ℕ) (φ : Vec m × ℝ → ℝ) (z : Vec m × ℝ) : ℝ :=
  fderiv ℝ (fun τ : ℝ => φ (z.1, τ)) z.2 1

end CIV
