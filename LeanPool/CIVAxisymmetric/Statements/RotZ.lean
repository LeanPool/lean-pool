/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Rot Z

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic


noncomputable section

namespace CIV

/-- The rotation `Q_φ` through the angle `φ` about the `z`-axis. -/
@[expose] def rotZ (φ : ℝ) (x : Vec3) : Vec3 :=
  ![Real.cos φ * x 0 - Real.sin φ * x 1, Real.sin φ * x 0 + Real.cos φ * x 1, x 2]

end CIV
