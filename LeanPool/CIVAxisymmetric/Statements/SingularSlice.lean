/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.IsBoundedNear

/-!
# Singular Slice

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic


noncomputable section

namespace CIV

/-- The singular slice of the blow-up time `t = 0`: the points near which `u` is
unbounded on every backward parabolic neighbourhood, `S₀` of design note R12. -/
@[expose] def singularSlice (u : ParabolicPoint → Vec3) : Set Vec3 := {x | ¬ IsBoundedNear u x}

end CIV
