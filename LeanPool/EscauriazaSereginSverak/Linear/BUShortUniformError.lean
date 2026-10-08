/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortUniformSizes

/-!
# Uniform short-time cutoff error bound

For radii at least one, the cutoff heat error has a fixed polynomial
height majorant and one explicit lower-time transition term.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A radius-independent coefficient for the heat cutoff error. -/
@[expose] def buShortUniformErrorCoeff (scale c₁ C₁ C₂ : ℝ) : ℝ :=
  (3 * (c₁ * scale) + 18) * buShortUniformGradientCoeff scale +
    buShortUniformHeatCoeff scale C₁ C₂

end ESS
