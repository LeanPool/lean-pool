/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PartialOdometerSquares

-- [TABLET NODE: PartialOdometerSlope]

/-!
# PartialOdometerSlope

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
If $S(h)$ is nonempty, the slope of a partial odometer $h$ is the average,
over $x\in S(h)$, of
$$
 \frac12\bigl(h(x+1)-h(x)+h(x+1+i)-h(x+i)\bigr)
 +\frac i2\bigl(h(x+i)-h(x)+h(x+1+i)-h(x+1)\bigr).
$$
We record this complex number by its ordered pair of real and imaginary
parts.  If $S(h)$ is empty, the slope is undefined.  In particular it is
undefined on a singleton domain, as required for the curvature-zero tile.
-/
noncomputable def PartialOdometerSlope
    (h : PartialOdometer) : Option (ℝ × ℝ) :=
-- BODY
  let S := PartialOdometerSquares h
  if S.Nonempty then
    some
      ((∑ x ∈ S,
          ((h.value (x + 1) - h.value x +
            h.value (x + 1 + ⟨0, 1⟩) - h.value (x + ⟨0, 1⟩) : ℤ) : ℝ)) /
          (2 * (S.card : ℝ)),
       (∑ x ∈ S,
          ((h.value (x + ⟨0, 1⟩) - h.value x +
            h.value (x + 1 + ⟨0, 1⟩) - h.value (x + 1) : ℤ) : ℝ)) /
          (2 * (S.card : ℝ)))
  else none

end ApollonianSuperharmonic

end
