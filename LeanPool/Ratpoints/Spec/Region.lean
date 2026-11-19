/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.WithBotTop

/-!
# The search region

The search region of `ratpoints`: search intervals `[l, u]` for `x / z`, whose ends are IEEE
binary64 doubles, given here by their bits, and a range of the denominators `z`. A double has a
value in `ℚ` extended by `⊥` and `⊤` (`WithBotTop ℚ`), the two infinities; a NaN has none (its value
here is junk), and both zeros have the value `0`; `ratpoints` refuses search intervals with a NaN
end, with `l > u` or that are not increasing and strictly apart. A point lies in the region when it
is at infinity, or its denominator is in the range and `x / z` lies in one of the intervals (in any,
when there are none). The specification uses Mathlib and nothing of the model; the comparator
challenge restates its definitions verbatim.

## Main definitions

* `Ratpoints.IsNaN`, `Ratpoints.doubleValue`: whether the bits of a double are a NaN, and the value
  of a double.
* `Ratpoints.AreSearchIntervals`, `Ratpoints.IntervalsWF`: closed intervals, increasing and
  strictly apart, over values and over the bits of doubles.
* `Ratpoints.InIntervals`: a rational number lies in one of a list of intervals.
* `Ratpoints.InRegion`: a point lies in the search region.
* `Ratpoints.IsFullBox`: the search region is the whole box of height `H`, so that `ratpoints` may
  reverse the polynomial.
* `Ratpoints.denominatorBound`: the largest denominator of the search.

## Implementation notes

The file imports `Mathlib.Order.WithBotTop` for the extended values and
`Mathlib.Algebra.Order.Field.Rat` for the order and the field operations of `ℚ`, both publicly: the
comparator challenge imports the Mathlib modules among the public imports of the files of the
specification that it restates, so that the definitions it restates elaborate to the same terms as
here.
-/

@[expose] public section

namespace Ratpoints

/-- Whether the IEEE binary64 bits `x` are a NaN: the exponent field all ones and the fraction
nonzero. -/
def IsNaN (x : UInt64) : Prop := (x.toNat / 2 ^ 52) % 2 ^ 11 = 2047 ∧ x.toNat % 2 ^ 52 ≠ 0

instance instDecidableIsNaN (x : UInt64) : Decidable (IsNaN x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The value of the IEEE binary64 double with the bits `x`: `±f 2 ^ (-1074)` for the exponent
field `0` (the zeros and the subnormals, both zeros giving `0`), `±(2 ^ 52 + f) 2 ^ (e - 1075)` for
an exponent field `e` from `1` to `2046`, and `⊥` and `⊤` for the infinities, where `f` is the
fraction and the sign is that of the top bit. The value of a NaN (the exponent field `2047` with a
nonzero fraction) is junk, an infinity: `Ratpoints.IntervalsWF` excludes NaNs. -/
def doubleValue (x : UInt64) : WithBotTop ℚ :=
  let e : ℕ := (x.toNat / 2 ^ 52) % 2 ^ 11
  let f : ℕ := x.toNat % 2 ^ 52
  if e = 2047 then (if 2 ^ 63 ≤ x.toNat then ⊥ else ⊤)
  else
    let a : ℚ := if e = 0 then f * 2 ^ (-1074 : ℤ) else (2 ^ 52 + f) * 2 ^ ((e : ℤ) - 1075)
    ((if 2 ^ 63 ≤ x.toNat then -a else a : ℚ) : WithBotTop ℚ)

/-- Closed intervals `[l, u]` with `l ≤ u`, increasing and strictly apart: the upper end of each
below the lower end of the next. -/
def AreSearchIntervals (dom : List (WithBotTop ℚ × WithBotTop ℚ)) : Prop :=
  (∀ i ∈ dom, i.1 ≤ i.2) ∧ dom.IsChain fun i j ↦ i.2 < j.1

instance instDecidableAreSearchIntervals (dom : List (WithBotTop ℚ × WithBotTop ℚ)) :
    Decidable (AreSearchIntervals dom) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The search intervals with the ends of the bits of doubles that `ratpoints` accepts, the test of
`RATPOINTS_BAD_ARGS`: no end is a NaN, and the values are closed intervals, increasing and strictly
apart (`Ratpoints.AreSearchIntervals`); `-0` and `0` have the same value. -/
def IntervalsWF (dom : List (UInt64 × UInt64)) : Prop :=
  (∀ i ∈ dom, ¬ IsNaN i.1 ∧ ¬ IsNaN i.2) ∧
    AreSearchIntervals (dom.map fun i ↦ (doubleValue i.1, doubleValue i.2))

instance instDecidableIntervalsWF (dom : List (UInt64 × UInt64)) : Decidable (IntervalsWF dom) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The rational number `x` lies in one of the intervals `D`, over the values of their ends, both
ends included. -/
def InIntervals (D : List (WithBotTop ℚ × WithBotTop ℚ)) (x : ℚ) : Prop :=
  ∃ i ∈ D, i.1 ≤ (x : WithBotTop ℚ) ∧ (x : WithBotTop ℚ) ≤ i.2

instance instDecidablePredInIntervals (D : List (WithBotTop ℚ × WithBotTop ℚ)) :
    DecidablePred (InIntervals D) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ D, _))

/-- The triple `p = (x, y, z)` lies in the search region of the intervals `dom` (over the values of
their ends) and the range of the denominators from `bLow` to `bHigh`: `z = 0` (a point at
infinity), or `bLow ≤ z`, `z ≤ bHigh` unless `bHigh < 1` (no bound beyond the height bound), and
`x / z` in one of the intervals (`Ratpoints.InIntervals`), or anywhere when there are none. -/
def InRegion (dom : List (WithBotTop ℚ × WithBotTop ℚ)) (bLow bHigh : ℤ) (p : ℤ × ℤ × ℤ) :
    Prop :=
  p.2.2 = 0 ∨ bLow ≤ p.2.2 ∧ (bHigh < 1 ∨ p.2.2 ≤ bHigh) ∧
    (dom = [] ∨ InIntervals dom (p.1 / p.2.2))

instance instDecidablePredInRegion (dom : List (WithBotTop ℚ × WithBotTop ℚ)) (bLow bHigh : ℤ) :
    DecidablePred (InRegion dom bLow bHigh) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The search region of the intervals `dom` and the range of the denominators from `bLow` to
`bHigh` is the whole box of the height bound `H`: no intervals, `bLow ≤ 1` and no bound below `H`
on the denominators (`bHigh < 1` or `H ≤ bHigh`). Only then may `ratpoints` reverse the polynomial
(otherwise it sets `RATPOINTS_NO_REVERSE_AUTO`). -/
def IsFullBox {α : Type*} (dom : List α) (bLow bHigh : ℤ) (H : ℕ) : Prop :=
  dom = [] ∧ bLow ≤ 1 ∧ (bHigh < 1 ∨ H ≤ bHigh)

instance instDecidableIsFullBox {α : Type*} (dom : List α) (bLow bHigh : ℤ) (H : ℕ) :
    Decidable (IsFullBox dom bLow bHigh H) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The largest denominator of the search for the bound `bHigh` and the height bound `H`: `bHigh`
when `1 ≤ bHigh ≤ H`, and `H` otherwise. -/
def denominatorBound (bHigh : ℤ) (H : ℕ) : ℕ :=
  if 1 ≤ bHigh ∧ bHigh ≤ H then bHigh.toNat else H

/-! ### Examples, checked by `decide` -/

-- The values of `1`, `-0.0`, `-∞`, `+∞`, the least subnormal `2 ^ (-1074)`, `2 ^ 63` and `-1.5`.
example : doubleValue 0x3ff0000000000000 = ((1 : ℚ) : WithBotTop ℚ) ∧
    doubleValue 0x8000000000000000 = ((0 : ℚ) : WithBotTop ℚ) ∧
    doubleValue 0xfff0000000000000 = ⊥ ∧ doubleValue 0x7ff0000000000000 = ⊤ ∧
    doubleValue 1 = (((2 : ℚ) ^ (-1074 : ℤ) : ℚ) : WithBotTop ℚ) ∧
    doubleValue 0x43e0000000000000 = (((2 : ℚ) ^ 63 : ℚ) : WithBotTop ℚ) ∧
    doubleValue 0xbff8000000000000 = ((-3 / 2 : ℚ) : WithBotTop ℚ) := by
  decide +kernel

-- `ratpoints` refuses a NaN end (`RATPOINTS_BAD_ARGS`), accepts `[-0.0, 0.0]` and `[0.0, -0.0]`,
-- refuses `[-1, -0.0]` followed by `[0.0, 1]` (not strictly apart), and accepts `[-∞, -∞]`.
example : ¬ IntervalsWF [(0x7ff8000000000000, 0x3ff0000000000000)] ∧
    IntervalsWF [(0x8000000000000000, 0)] ∧ IntervalsWF [(0, 0x8000000000000000)] ∧
    ¬ IntervalsWF [(0xbff0000000000000, 0x8000000000000000), (0, 0x3ff0000000000000)] ∧
    IntervalsWF [(0xfff0000000000000, 0xfff0000000000000)] := by
  decide +kernel

-- `1 / 3` lies in `[-0.5, 0.5]` and `2 / 3` does not; a point at infinity lies in every region;
-- the denominators from `2` to `5`, and from `2` on.
example :
    InRegion [(doubleValue 0xbfe0000000000000, doubleValue 0x3fe0000000000000)] 1 0 (1, 7, 3) ∧
    ¬ InRegion [(doubleValue 0xbfe0000000000000, doubleValue 0x3fe0000000000000)] 1 0 (2, 7, 3) ∧
    InRegion [(⊤, ⊤)] 5 3 (1, 2, 0) ∧ ¬ InRegion [] 2 5 (0, 1, 1) ∧ InRegion [] 2 5 (7, 1, 5) ∧
    ¬ InRegion [] 2 5 (7, 1, 6) ∧ InRegion [] 2 0 (7, 1, 6) := by
  decide +kernel

end Ratpoints

end
