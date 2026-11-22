/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.C19Geometry
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! # Quantized characters of the finite cubic torus -/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

/-- The native momentum labels of the finite cubic torus.  This has exactly
`L ^ 3` elements, the same number as `PeriodicCubicSite L`. -/
abbrev PeriodicCubicMomentum (L : ℕ) := Fin 3 → ZMod L

/-- The product character of the three cyclic axes, written as one standard
additive character. -/
def periodicQuantizedCharacter (L : ℕ) [NeZero L]
    (mode : PeriodicCubicMomentum L) (site : PeriodicCubicSite L) : ℂ :=
  ZMod.stdAddChar (∑ axis : Fin 3, mode axis * site axis)

end
end LeanDirac.V2
