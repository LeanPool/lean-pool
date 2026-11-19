/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Order.WithBotTop

/-!
# The order of `WithBotTop`

Candidates for `Mathlib.Order.WithBotTop`: an element of the type lies strictly between `⊥` and
`⊤` (`WithBotTop.bot_lt_coe`, `WithBotTop.coe_lt_top`).
-/

@[expose] public section

namespace WithBotTop

variable {ι : Type*}

@[simp]
theorem bot_lt_coe [LT ι] (a : ι) : (⊥ : WithBotTop ι) < a :=
  WithBot.bot_lt_coe _

@[simp]
theorem coe_lt_top [LT ι] (a : ι) : (a : WithBotTop ι) < ⊤ :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)

end WithBotTop

end
