/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PartialOdometer

-- [TABLET NODE: OdometerCompatibility]

/-!
# OdometerCompatibility

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Two partial odometers $h_1,h_2$ are compatible if their domains are
disjoint, or if there is an integer $c$ such that
$$
 h_2(x)-h_1(x)=c
$$
for every $x\in T(h_1)\cap T(h_2)$.  When the intersection is nonempty,
$c$ is the offset constant of the ordered pair $(h_1,h_2)$.
-/
def OdometerCompatibility (h₁ h₂ : PartialOdometer) : Prop :=
-- BODY
  Disjoint (h₁.domain : Set GaussianInt) (h₂.domain : Set GaussianInt) ∨
    ∃ c : ℤ, ∀ x, x ∈ h₁.domain → x ∈ h₂.domain →
      h₂.value x - h₁.value x = c

end ApollonianSuperharmonic

end
