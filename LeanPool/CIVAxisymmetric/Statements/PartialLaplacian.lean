/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Partial Laplacian

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN


noncomputable section

namespace CIV

/-- The Laplacian in the first `d` coordinates of a test function on `Vec m × ℝ`. -/
@[expose] def partialLaplacian (m d : ℕ) (φ : Vec m × ℝ → ℝ) (z : Vec m × ℝ) : ℝ :=
  ∑ i : Fin m, if (i : ℕ) < d then
    fderiv ℝ (fun x : Vec m => fderiv ℝ (fun y : Vec m => φ (y, z.2)) x (basisVec i)) z.1
      (basisVec i)
  else 0

end CIV
