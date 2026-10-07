/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import Mathlib.GroupTheory.FreeGroup.Basic

/-! The shared right factor, free basis and lift used by the amalgam and normal-form models. -/

@[expose] public section

namespace Undecidability.Gordon

/-- The common free basis used to describe Gordon's uncompressed
free-product-with-amalgamation presentation. -/
inductive BasisIndex (n : ℕ)
  | conjugateA
  | conjugateAlpha
  | old (i : Fin n)
  | commutator
  deriving DecidableEq

/-- The right free factor used to construct the amalgam. -/
abbrev RightFactor := FreeGroup (Fin 2)

/-- The free generator `b` of the right-hand factor. -/
def rightB : RightFactor := FreeGroup.of (0 : Fin 2)
/-- The free generator `beta` of the right-hand factor. -/
def rightBeta : RightFactor := FreeGroup.of (1 : Fin 2)

/-- Gordon's right-hand conjugate `beta^(-r) * b * beta^r`. -/
def rightU (r : ℕ) : RightFactor :=
  (rightBeta ^ r)⁻¹ * rightB * rightBeta ^ r

/-- The right-hand amalgamating elements in Gordon's construction. -/
def rightBasis {n : ℕ} : BasisIndex n → RightFactor
  | .conjugateA => rightB ^ 2
  | .conjugateAlpha => rightB * rightBeta * rightB⁻¹
  | .old i => rightU (i.1 + 1)
  | .commutator => rightU (n + 1)

/-- The homomorphism freely extending Gordon’s right-hand amalgamating basis. -/
def rightBasisMap (n : ℕ) : FreeGroup (BasisIndex n) →* RightFactor :=
  FreeGroup.lift rightBasis

end Undecidability.Gordon
