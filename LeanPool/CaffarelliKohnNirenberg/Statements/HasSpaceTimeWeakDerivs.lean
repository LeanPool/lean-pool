/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Has Space Time Weak Derivs

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- Space-time weak derivatives on `Ω × I`: `Dw z i j` is `∂ⱼ wᵢ`, `D2w z i j k` is
`∂ₖ ∂ⱼ wᵢ`, and `Dtw z i` is `∂ₜ wᵢ`, each defined by integration by parts against
smooth compactly supported scalar tests on `Ω × I`; all four fields are locally
integrable on `Ω × I` (manuscript §2, space-time weak derivatives). -/
@[expose]
def HasSpaceTimeWeakDerivs (Ω : Set Vec3) (I : Set ℝ) (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3) (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3) : Prop :=
  LocallyIntegrableOn w (spaceTimeSet Ω I) ∧ LocallyIntegrableOn Dw (spaceTimeSet Ω I) ∧
  LocallyIntegrableOn D2w (spaceTimeSet Ω I) ∧ LocallyIntegrableOn Dtw (spaceTimeSet Ω I) ∧
  ∀ φ : ParabolicPoint → ℝ, φ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
    (∀ i j : Fin 3,
      ∫ z in spaceTimeSet Ω I, w z i * spatialPartial φ j z =
        -∫ z in spaceTimeSet Ω I, Dw z i j * φ z) ∧
    (∀ i j k : Fin 3,
      ∫ z in spaceTimeSet Ω I, Dw z i j * spatialPartial φ k z =
        -∫ z in spaceTimeSet Ω I, D2w z i j k * φ z) ∧
    (∀ i : Fin 3,
      ∫ z in spaceTimeSet Ω I, w z i * timePartial φ z =
        -∫ z in spaceTimeSet Ω I, Dtw z i * φ z)

end CKN
