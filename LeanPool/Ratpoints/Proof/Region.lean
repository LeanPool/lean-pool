/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Model.Double
public import LeanPool.Ratpoints.Spec.Basic
public import LeanPool.Ratpoints.Spec.Region

/-!
# Representing search intervals and the full search box
-/

@[expose] public section

namespace Ratpoints

/-- The values of the ends of the search intervals `dom` of the model (`Ratpoints.doubleValue`). -/
abbrev domainValues (dom : List (Double × Double)) : List (WithBotTop ℚ × WithBotTop ℚ) :=
  dom.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)

/-- The bits of the ends of the search intervals `dom` of the model. -/
abbrev domainBits (dom : List (Double × Double)) : List (UInt64 × UInt64) :=
  dom.map fun i ↦ (i.1.bits, i.2.bits)

/-- A pair `(x, z)` of height at most `H` lies in the search region of the whole box. -/
theorem inRegion_of_isFullBox {D : List (WithBotTop ℚ × WithBotTop ℚ)} {bLow bHigh : ℤ} {H : ℕ}
    (hb : IsFullBox D bLow bHigh H) {p : ℤ × ℤ × ℤ} (hz : 0 ≤ p.2.2) (hzH : p.2.2 ≤ H) :
    InRegion D bLow bHigh p := by
  obtain ⟨hD, h1, h2⟩ := hb
  rcases eq_or_lt_of_le hz with h0 | h0
  · exact .inl h0.symm
  · exact .inr ⟨by lia, by lia, .inl hD⟩

/-- A normalized pair `(x, z)` of height at most `H` lies, with any `y`, in the search region of the
whole box. -/
theorem IsNormalizedPair.inRegion_of_isFullBox {H : ℕ} {p : ℤ × ℤ × ℤ}
    (hn : IsNormalizedPair H p.1 p.2.2) {D : List (WithBotTop ℚ × WithBotTop ℚ)} {bLow bHigh : ℤ}
    (hb : IsFullBox D bLow bHigh H) : InRegion D bLow bHigh p :=
  Ratpoints.inRegion_of_isFullBox hb (hn.2.1.elim (·.le) (·.1.ge)) hn.2.2.2

theorem IsFullBox.map {α β : Type*} {dom : List α} {bLow bHigh : ℤ} {H : ℕ}
    (h : IsFullBox dom bLow bHigh H) (f : α → β) : IsFullBox (dom.map f) bLow bHigh H :=
  ⟨List.map_eq_nil_iff.mpr h.1, h.2⟩

end Ratpoints

end
