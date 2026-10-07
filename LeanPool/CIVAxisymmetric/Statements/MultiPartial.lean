/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial

/-!
# Multi Partial

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The multi-index spatial derivative `∂_x^α g`. -/
@[expose] def multiPartial (g : ParabolicPoint → ℝ) (α : Fin 3 → ℕ) : ParabolicPoint → ℝ :=
  (fun k => spatialPartial k 0)^[α 0]
    ((fun k => spatialPartial k 1)^[α 1] ((fun k => spatialPartial k 2)^[α 2] g))

end CIV
