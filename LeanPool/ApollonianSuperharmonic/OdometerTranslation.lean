/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PartialOdometer

-- [TABLET NODE: OdometerTranslation]

/-!
# OdometerTranslation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Two partial odometers $h_1,h_2$ are odometer translations of one another
if there are $v,a\in\mathbb Z[i]$ and $b\in\mathbb Z$ such that
$$
 T(h_1)=T(h_2)+v
 \quad\text{and}\quad
 h_1(x)=h_2(x-v)+a\mathbin{\cdot}x+b
$$
for every $x\in T(h_1)$, where
$a\mathbin{\cdot}x=\operatorname{Re}(a)\operatorname{Re}(x)
+\operatorname{Im}(a)\operatorname{Im}(x)$.
-/
def OdometerTranslation (h₁ h₂ : PartialOdometer) : Prop :=
-- BODY
  ∃ v a : GaussianInt, ∃ b : ℤ,
    (∀ x, x ∈ h₁.domain ↔ x - v ∈ h₂.domain) ∧
    ∀ x, x ∈ h₁.domain →
      h₁.value x = h₂.value (x - v) +
        a.re * x.re + a.im * x.im + b

end ApollonianSuperharmonic

end
