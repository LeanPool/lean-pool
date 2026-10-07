/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

/-!
# Force C2 Bounded

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The force is bounded in `C²` up to the blow-up time, `eq:interior:force:c-two`. -/
@[expose] def ForceC2Bounded (f : ParabolicPoint → Vec3) : Prop :=
  ∃ M : ℝ, ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
    |multiPartial (fun w => f w i) α z| ≤ M

end CIV
