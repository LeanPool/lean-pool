/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction

-- [TABLET NODE: PartialOdometer]

/-!
# PartialOdometer

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A partial odometer is an integer-valued function on a finite subset
$T\subseteq\mathbb Z[i]$.  Formally, we represent it by its finite domain
and by the extension of its values by zero outside that domain; values
outside the displayed domain are not part of the partial function.
-/
structure PartialOdometer where
-- BODY
  /-- The finite set of lattice vertices where the partial function is defined. -/
  domain : Finset GaussianInt
  /-- The integer value function, extended by zero outside the finite domain. -/
  value : IntegerLatticeFunction
  value_outside : ∀ x, x ∉ domain → value x = 0

end ApollonianSuperharmonic

end
