/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.GaussianTranslation
public import LeanPool.ApollonianSuperharmonic.PartialOdometer

-- [TABLET NODE: PartialOdometerAffineTranslate]

/-!
# PartialOdometerAffineTranslate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a partial odometer $h$, Gaussian integers $u,a$, and $b\in\mathbb Z$,
the affine spatial translate
$\operatorname{AffTr}_{u,a,b}(h)$ has domain
$\tau_u(T(h))$, where $\tau_u(x)=x+u$.  At a point of this translated
domain its value is
$$
 h(x-u)+\operatorname{Re}(a)\operatorname{Re}(x)
       +\operatorname{Im}(a)\operatorname{Im}(x)+b.
$$
Its total-function representative has value zero outside the translated
domain.
-/
def PartialOdometerAffineTranslate (h : PartialOdometer)
    (u a : GaussianInt) (b : ℤ) : PartialOdometer :=
-- BODY
  { domain := h.domain.image (GaussianTranslation u)
    value := fun x =>
      if x ∈ h.domain.image (GaussianTranslation u) then
        h.value (x - u) + a.re * x.re + a.im * x.im + b
      else 0
    value_outside := by
      intro x hx
      simp [hx] }

end ApollonianSuperharmonic

end
