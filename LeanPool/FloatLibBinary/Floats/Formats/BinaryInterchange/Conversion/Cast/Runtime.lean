/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
Upstream FloatLib code retains its MIT license below. The Lean Pool integration changes are
covered by the standard header above.

MIT License

Copyright (c) 2026 FloatLib

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Conversion.Cast.Widening
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Status.Runtime

/-!
# Executable binary format casts

Convert a value from one binary descriptor (`src`) to another (`dst`), for example binary32 to
bfloat16 or binary16 to binary64. Conversion uses the source encoding's exact value, without a
host floating-point intermediate.

## Finite values

Normal numbers, subnormals, and zeros decode to a signed dyadic:

```text
(±)  mant × 2^exp
```

The integer significand and power-of-two scale represent the source value exactly. Binary32
`1.0` decodes to exactly `1`; binary32 `0.1` decodes to the already rounded binary32 value.
Widening the latter preserves that value, including its difference from the rational `1/10`.

`cast` rounds once to nearest, with ties to even, in the destination. `castWithRounding` accepts
an explicit rounding mode. Identity casts and compatible fraction-field widenings bypass rounding
because they preserve every finite source value exactly.

| Situation | Result |
|-----------|--------|
| The destination represents the source value | Exact conversion, including binary16 to binary32 |
| The source lies between destination values | One rounding step in the selected mode |
| The magnitude exceeds the destination range | The destination encoding's overflow behavior |
| The magnitude is below the smallest normal | A subnormal or zero, according to rounding |

The general finite path is:

```text
Model src
    │  finiteDyadic
    ▼
  Numerics.Dyadic  (± mant × 2^exp)     -- exact meaning of the source bits
    │  roundDyadic dst                -- or roundDyadicWithRounding
    ▼
Model dst
```

## NaNs and infinities

A NaN cast to the same descriptor is quieted while retaining its representable payload.
Across unequal descriptors, conversion uses `invalidResult dst`: the destination's canonical NaN
when available, or positive zero for a fully finite encoding. Neither the source NaN sign nor its
payload is transported across unequal descriptors, even when their field widths agree.

Infinity follows the destination's overflow policy: same-sign infinity for IEEE encodings,
canonical NaN for finite-with-NaN encodings, and the same-sign maximum finite value for a fully
finite encoding.

Once NaN and infinity have been excluded, finiteness is proved and `finiteDyadic` is total.
`castWithStatus` also reports invalid input, overflow, underflow, and inexactness according to the
same conversion result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Widen a finite value when source and destination have the same exponent semantics.

The exponent field is copied and the source fraction is shifted into the high end of the wider
destination fraction. Equal exponent width, bias, and encoding make this field copy
value-preserving. The hypotheses are retained in the term so callers cannot accidentally use this
operation as a narrowing conversion or cross an encoding boundary.
-/
@[inline] def widenExact {src dst : FloatFormat} (x : Model src)
    (_ : src.expWidth = dst.expWidth)
    (_ : src.exponentBias = dst.exponentBias)
    (_ : src.encoding = dst.encoding)
    (_ : src.fracWidth ≤ dst.fracWidth) : Model dst :=
  let shift := dst.fracWidth - src.fracWidth
  ofFields dst (signBit x) (expField x)
    (Nat.shiftLeft (fracField x) shift)

/-- Implement compatible widening with one shift of the complete stored word. -/
@[inline] def widenExactImpl {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (_ : src.exponentBias = dst.exponentBias)
    (_ : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth) : Model dst :=
  widenBits x hexp hfrac

/--
The compiler uses the whole-word shift in every caller of compatible widening.

This equality covers every bit pattern; the surrounding cast retains its NaN and infinity policy.
It is registered before the public casts are compiled.
-/
@[csimp] theorem widenExact_eq_widenExactImpl : @widenExact = @widenExactImpl := by
  funext src dst x hexp hbias hencoding hfrac
  exact (widenBits_eq_ofFields x hexp hfrac).symm

/--
Cast `x` from format `src` into format `dst`.

**Finite values:** decode the source bits to an exact dyadic (`mant × 2^exp`), then
pack that value into `dst` with round-to-nearest, ties-to-even (`roundDyadic`).
Out-of-range magnitudes follow the destination encoding's overflow and underflow rules;
coarser precision can introduce rounding error.

**Inf:** the destination's native overflow result, just as for an overflowing finite input:
same-sign infinity for IEEE encodings, NaN for finite-with-NaN encodings, and the same-sign maximum
finite value for fully finite encodings. Saturating conversion is an explicit policy in
`ExecFloat.Binary.Conversion.Context`.

**NaN:** if `src = dst`, quiet the existing encoding while retaining its representable payload.
Otherwise emit the destination's canonical NaN when it has one, or positive zero for a finite-only
destination. Payloads are not remapped across unequal formats.

**Finite, `src = dst`:** short-circuits to `x` unchanged. Decoding to a dyadic and
rounding back into the same grid is a true identity for finite values, so this skips the
decode/round work entirely. This matters for uniform-format `SitePolicy`s, where `mulAcc` and
`dotSequential` cast every operand even though storage, product, and accumulator formats agree.
-/
@[inline] def cast (src dst : FloatFormat) (x : Model src) : Model dst :=
  if hnan : isNaN x = true then
    if h : src = dst then
      -- The dependent equality transports the exact-width payload without truncation.
      h ▸ quietNaN x
    else
      invalidResult dst
  else if hinf : isInf x = true then
    nativeOverflow dst (signBit x)
  else
    have hfinite : isFinite x = true :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x
        (Bool.eq_false_of_not_eq_true hnan)
        (Bool.eq_false_of_not_eq_true hinf)
    if h : src = dst then
      h ▸ x
    else if hexp : src.expWidth = dst.expWidth then
      if hbias : src.exponentBias = dst.exponentBias then
        if hencoding : src.encoding = dst.encoding then
          if hfrac : src.fracWidth ≤ dst.fracWidth then
            widenExact x hexp hbias hencoding hfrac
          else
            roundDyadic dst (finiteDyadic x hfinite)
        else
          roundDyadic dst (finiteDyadic x hfinite)
      else
        roundDyadic dst (finiteDyadic x hfinite)
    else
      roundDyadic dst (finiteDyadic x hfinite)

/--
Cast `x` using any IEEE rounding direction.

NaNs and infinities follow the same explicit value-class policy as `cast`, because a rounding
direction has no numerical effect on them. Finite identity casts and compatible widenings remain
exact fast paths. Every other finite conversion decodes once to an exact dyadic and rounds once in
the destination format.
-/
@[inline] def castWithRounding (src dst : FloatFormat) (x : Model src)
    (mode : IEEERoundingMode := .nearestEven) : Model dst :=
  match mode with
  | .nearestEven => cast src dst x
  | mode =>
      if hnan : isNaN x = true then
        cast src dst x
      else if hinf : isInf x = true then
        cast src dst x
      else
        have hfinite : isFinite x = true :=
          isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x
            (Bool.eq_false_of_not_eq_true hnan)
            (Bool.eq_false_of_not_eq_true hinf)
        if h : src = dst then
          h ▸ x
        else if hexp : src.expWidth = dst.expWidth then
          if hbias : src.exponentBias = dst.exponentBias then
            if hencoding : src.encoding = dst.encoding then
              if hfrac : src.fracWidth ≤ dst.fracWidth then
                widenExact x hexp hbias hencoding hfrac
              else
                roundDyadicWithRounding dst mode (finiteDyadic x hfinite)
            else
              roundDyadicWithRounding dst mode (finiteDyadic x hfinite)
          else
            roundDyadicWithRounding dst mode (finiteDyadic x hfinite)
        else
          roundDyadicWithRounding dst mode (finiteDyadic x hfinite)

/--
Cast `x` and report the IEEE exception indicators raised by the conversion.

A signaling NaN raises invalid. A quiet NaN raises invalid only when the destination cannot
represent a NaN at all. Infinity is exact when the destination preserves infinity. A destination
without infinity reports overflow and inexactness, including when its overflow encoding is a NaN;
this conversion does not raise invalid. Finite values use the same exact dyadic witness for both
directed rounding and status classification.
-/
def castWithStatus (src dst : FloatFormat) (x : Model src)
    (mode : IEEERoundingMode := .nearestEven) : IEEEOutcome dst :=
  let value := castWithRounding src dst x mode
  if hnan : isNaN x = true then
    outcomeWithInvalid value (isSNaN x || !isNaN value)
  else if hinf : isInf x = true then
    if isInf value then
      { value, status := .clear }
    else
      { value, status := { overflow := true, inexact := true } }
  else
    have hfinite : isFinite x = true :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x
        (Bool.eq_false_of_not_eq_true hnan)
        (Bool.eq_false_of_not_eq_true hinf)
    let exact := finiteDyadic x hfinite
    { value, status := dyadicRoundingStatus dst mode exact value }

end Model
end FloatLib.Floats.Formats.BinaryInterchange
