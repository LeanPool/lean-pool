/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PartialOdometer

-- [TABLET NODE: PartialOdometerHalfTurn]

/-!
# PartialOdometerHalfTurn

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The origin half-turn of a partial odometer $h$ is the partial odometer
$h^{-}$ with domain $-\operatorname{dom}(h)$ and values
$h^{-}(x)=h(-x)$.  Its stored total-function representative is set to zero
outside that reflected finite domain, as required by
`PartialOdometer`.
-/
def PartialOdometerHalfTurn (h : PartialOdometer) : PartialOdometer :=
-- BODY
  { domain := h.domain.image (fun x => -x)
    value := fun x => if -x ∈ h.domain then h.value (-x) else 0
    value_outside := by
      intro x hx
      split
      next hmem =>
        exfalso
        apply hx
        exact Finset.mem_image.mpr ⟨-x, hmem, by simp⟩
      next => rfl }

end ApollonianSuperharmonic

end
