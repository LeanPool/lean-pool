/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AngularMean

/-!
# Is Axisymmetric On

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic


noncomputable section

namespace CIV

/-- A field is axisymmetric on a set when its non-axisymmetric part `w = u - 𝒫u`
vanishes there (Section `sec:aniso:notation`). -/
@[expose] def IsAxisymmetricOn (u : ParabolicPoint → Vec3) (S : Set ParabolicPoint) : Prop :=
  ∀ z ∈ S, angularMean u z = u z

end CIV
