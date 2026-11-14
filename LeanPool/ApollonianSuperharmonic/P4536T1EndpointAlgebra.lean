/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Ring

public import Mathlib.Tactic.LinearCombination

-- [TABLET NODE: P4536T1EndpointAlgebra]

/-!
# P4536T1EndpointAlgebra

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4536T1EndpointAlgebra {R : Type*} [CommRing R]
    (e w x y : R) (he : e ^ 2 = -1) (hs : w + x + y = 0) :
    (-(w - e * w) - ((x - e * y) - e * (x - e * y)) = 2 * y) ∧
    ((x - e * y) + e * (x - e * y) + (w - e * w) = 2 * e * x) ∧
    (-(x - e * x) - (w - e * w) = y - e * y) ∧
    ((y - e * w) + e * (y - e * w) - (w - e * w) = y + e * y) ∧
    ((w - e * x) - e * (w - e * x) - (w - e * w) = -e * x - x) ∧
    (-(y - e * y) - (w - e * w) = -e * x + x) ∧
    ((y - e * w) - e * (y - e * w) - (y - e * y) = -e * w - w) ∧
    (-(x - e * x) - (y - e * y) = -e * w + w) ∧
    (-(y - e * y) - (x - e * x) = w - e * w) ∧
    ((w - e * x) + e * (w - e * x) - (x - e * x) = w + e * w) := by
-- BODY
  have hw : w = -x - y := by linear_combination hs
  subst w
  constructor
  · linear_combination -y * he
  constructor
  · linear_combination -y * he
  constructor
  · ring
  constructor
  · linear_combination (x + y) * he
  constructor
  · linear_combination x * he
  constructor
  · ring
  constructor
  · linear_combination -(x + y) * he
  constructor
  · ring
  constructor
  · ring
  · linear_combination -x * he

end ApollonianSuperharmonic

end
