/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial

/-!
# Meridional Partial

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The iterated classical partial derivative `∂₁^a ∂₃^b g`. On the meridional plane it is
`±∂_r^a ∂_z^b g` for an axisymmetric scalar `g` (design note R4). -/
@[expose] def meridionalPartial (g : ParabolicPoint → ℝ) (a b : ℕ) : ParabolicPoint → ℝ :=
  (fun k => spatialPartial k 0)^[a] ((fun k => spatialPartial k 2)^[b] g)

end CIV
