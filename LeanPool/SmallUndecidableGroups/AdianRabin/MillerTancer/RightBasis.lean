/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import Mathlib.GroupTheory.FreeGroup.Basic

/-! The shared right factor, free basis and lift used by the amalgam and normal-form models. -/

@[expose] public section

namespace Undecidability.MillerTancer

/-- The right free factor used to construct the amalgam. -/
abbrev RightFactor := FreeGroup (Fin 2)

/-- The right-factor free generator `beta`. -/
def rightBeta : RightFactor := FreeGroup.of (0 : Fin 2)
/-- The right-factor free generator `gamma`. -/
def rightGamma : RightFactor := FreeGroup.of (1 : Fin 2)

/-- The five right-hand amalgamating generators of the Miller–Tancer construction. -/
def rightBasis : Fin 5 → RightFactor
  | 0 => rightBeta
  | 1 => rightGamma⁻¹ * rightBeta⁻¹ * rightGamma * rightBeta * rightGamma
  | 2 => (rightGamma ^ 2)⁻¹ * rightBeta⁻¹ * rightGamma * rightBeta * rightGamma ^ 2
  | 3 => (rightGamma ^ 3)⁻¹ * rightBeta * rightGamma ^ 3
  | 4 => (rightGamma ^ 4)⁻¹ * rightBeta * rightGamma ^ 4

/-- The homomorphism freely extending the five right-hand amalgamating generators. -/
def rightBasisMap : FreeGroup (Fin 5) →* RightFactor :=
  FreeGroup.lift rightBasis

end Undecidability.MillerTancer
