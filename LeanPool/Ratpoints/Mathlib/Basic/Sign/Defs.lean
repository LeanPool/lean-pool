/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Basic.Sign.Defs

/-!
# A sign that is zero after its cast

A candidate for `Mathlib.Basic.Sign.Defs`: the cast of a sign into a type in which `1 ≠ 0`, such as
`ℤ`, is `0` only for the sign `0` (`SignType.coe_eq_zero`), so that with `sign_eq_zero_iff` the
integer sign of `a` is `0` exactly for `a = 0`.

## Main statements

* `SignType.coe_eq_zero`: the cast of a sign is `0` only for the sign `0`.
-/

@[expose] public section

namespace SignType

@[simp]
theorem coe_eq_zero {α : Type*} [One α] [SubtractionMonoid α] [NeZero (1 : α)] {s : SignType} :
    (s : α) = 0 ↔ s = 0 := by
  cases s <;> simp

end SignType

end
