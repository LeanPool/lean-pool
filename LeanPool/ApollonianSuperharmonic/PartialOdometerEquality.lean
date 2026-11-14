/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PartialOdometer
public import Mathlib.Init


/-!
# PartialOdometerEquality

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace PartialOdometerEquality

/-- Equal domains and values determine the partial odometer. -/
theorem extensionality (h k : PartialOdometer)
    (hdom : (h.domain : Set GaussianInt) = k.domain) (hvalue : ∀ x, h.value x = k.value x) :
    h = k := by
  cases h with
  | mk hd hv hout =>
    have hdomEq : hd = k.domain := Finset.coe_injective hdom
    have hvalEq : hv = k.value := funext hvalue
    cases hdomEq
    cases hvalEq
    rfl

end PartialOdometerEquality
end ApollonianSuperharmonic

end
