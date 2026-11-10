/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Data.ENat.Basic

import Mathlib.Data.ENat.Monoid

/-!
# Additions to the `ℕ∞` API

A single Mathlib-gap fact: from an identity `a + b = ↑n` of extended naturals one recovers the
`ℕ`-level identity `a.toNat + b.toNat = n` (`ENat.toNat_add_toNat_of_add_eq_natCast`).
-/

@[expose] public section

namespace ENat

/-- Extracting the two `ℕ`-values from an `ℕ∞`-identity `a + b = ↑n`. -/
theorem toNat_add_toNat_of_add_eq_natCast {a b : ℕ∞} {n : ℕ} (h : a + b = ↑n) :
    a.toNat + b.toNat = n := by
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top (natCast_ne_top n) (h ▸ le_self_add)
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top (natCast_ne_top n) (h ▸ le_add_self)
  rw [← toNat_add ha hb, h, toNat_natCast]

end ENat

end
