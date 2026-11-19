/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The doubles of the C code

The C code of `ratpoints` holds the ends of its search intervals as `double`s: the intervals of the
caller (`args->domain`), the default interval `[-h, h]` of the library and the ends of the intervals
that the Sturm step keeps. Apart from the estimate of the work in the choice of the moduli
(`numerators_for`, `Ratpoints.numeratorsFor`, where the ends enter the arithmetic of Lean's `Float`
by their bits, `Ratpoints.Double.toFloat`), it does no floating-point arithmetic on them: it
converts `long`s to doubles, compares doubles, takes them apart into mantissa and exponent
(`frexp`), scales them by powers of 2 (`ldexp`), steps to the next double (`nextafter`), converts
doubles to `long`s and `unsigned long`s, and prints them, as `printf` of glibc does under the
conversions `%f` and `%.pf` (`Ratpoints.Double.printFixed`); the report of the library prints
doubles of its cost model too (`Ratpoints.Double.ofFloat`). The model holds a double as its IEEE 754
binary64 bits (`Ratpoints.Double`), with these operations as functions on the bits, each doing what
the operation of the C language or the C library does to a double on the platforms of `ratpoints`
(IEEE 754 binary64 with rounding to nearest, ties to even, as gcc and glibc implement them): the
comparisons, in which a NaN is unordered and `-0.0` equals `0.0`, the negation and `fabs`, which act
on the sign bit, the conversions, `frexp`, `ldexp` and `nextafter` towards `±HUGE_VAL`, but for a
signalling NaN, which glibc's `frexp`, `ldexp` and `nextafter` return quieted and the model as it is
(`ratpoints` passes them no NaN). The exact value of a finite double is `m 2 ^ e` for the integers
of `Ratpoints.Double.toDyadic`, and a dyadic number is rounded to a double, to nearest with ties to
even, by `Ratpoints.Double.ofDyadic`, a fraction by `Ratpoints.Double.ofRatio` (for `strtod`, which
the program uses).

## Main definitions

* `Ratpoints.Double`: a C `double`, by its bits.
* `Ratpoints.Double.isNaN`, `Ratpoints.Double.isInf`, `Ratpoints.Double.isFinite`: the NaNs, the
  infinities and the finite doubles.
* `Ratpoints.Double.lt`, `Ratpoints.Double.le`, `Ratpoints.Double.beq`: the comparisons `<`, `<=`
  and `==` of the C language on doubles.
* `Ratpoints.Double.neg`, `Ratpoints.Double.fabs`: the negation and the absolute value.
* `Ratpoints.Double.toDyadic`, `Ratpoints.Double.ofDyadic`: the exact value of a finite double, and
  the double nearest to a dyadic number.
* `Ratpoints.Double.toRat`, `Ratpoints.Double.ofRatio`: the exact value of a finite double as a
  rational number, and the double nearest to a fraction.
* `Ratpoints.Double.assemble`, `Ratpoints.Double.ofSignificand`: the double of a significand and
  the exponent of its last place, the last step of both roundings.
* `Ratpoints.Double.ofInt64`, `Ratpoints.Double.toInt64`, `Ratpoints.Double.toUInt64`: the
  conversions between `long`s and doubles.
* `Ratpoints.Double.ldexp`, `Ratpoints.Double.frexp`, `Ratpoints.Double.nextUp`,
  `Ratpoints.Double.nextDown`: the functions of the C library.
* `Ratpoints.Double.toFloat`, `Ratpoints.Double.ofFloat`: a double as a value of Lean's `Float`,
  for the cost model of the choice of the moduli, and back, for the report of the library.
* `Ratpoints.Double.printFixed`: a double as `printf` prints it under `%.pf`.
-/

@[expose] public section

namespace Ratpoints

/-- A C `double`, by its IEEE 754 binary64 bits: the sign bit (bit 63), the biased exponent (bits 52
to 62) and the fraction (bits 0 to 51). Equality of the bits is not the `==` of the C language,
under which `-0.0` equals `0.0` and a NaN equals nothing; that is `Ratpoints.Double.beq`. -/
structure Double where
  /-- The 64 bits of the double. -/
  bits : UInt64
  deriving Inhabited, Repr

namespace Double

/-- `DBL_MANT_DIG` of `float.h`, the number of bits of the significand of a double, `53`: a fact of
the format, not a parameter of `ratpoints`. -/
def mantDig : Nat := 53

/-- `0.0`. -/
def zero : Double := ⟨0⟩

/-- `HUGE_VAL` of `math.h`, which is `+∞` for the doubles of IEEE 754. -/
def huge : Double := ⟨0x7ff0000000000000⟩

/-- The double `2 ^ 63`, the literal `9223372036854775808.0` of the C code. -/
def twoPow63 : Double := ⟨0x43e0000000000000⟩

/-- The double `-1.0`, the literal `-1.0` with which `main.c` sets the tuning fields of the
arguments that are doubles, meaning "the default" (`Ratpoints.SieveOptions`). -/
def minusOne : Double := ⟨0xbff0000000000000⟩

/-- The double `x` as a value of Lean's `Float`, the IEEE 754 binary64 type with the arithmetic of
the platform, by its bits: the doubles that the caller gives the cost model of the choice of the
moduli enter its arithmetic so, the tuning values of the options of the sieve
(`Ratpoints.SieveOptions`) and the ends of the search intervals (`Ratpoints.numeratorsFor`). -/
def toFloat (x : Double) : Float := Float.ofBits x.bits

/-- The value `x` of Lean's `Float` as a double, by its bits: the doubles of the cost model of the
choice of the moduli that the report of the library prints (`Ratpoints.Report.choice`,
`Ratpoints.Report.moduli`). -/
def ofFloat (x : Float) : Double := ⟨x.toBits⟩

/-- The sign bit. -/
def signBit (x : Double) : Bool := x.bits >>> 63 == 1

/-- The biased exponent, from `0` (zeros and subnormals) to `2047` (infinities and NaNs). -/
def expField (x : Double) : Nat := ((x.bits >>> 52) &&& 0x7ff).toNat

/-- The fraction, the 52 low bits. -/
def fracField (x : Double) : Nat := (x.bits &&& 0xfffffffffffff).toNat

/-- Whether `x` is a NaN, as `isnan` of `math.h` decides it: the largest exponent and a fraction
that is not zero. -/
def isNaN (x : Double) : Bool := x.expField == 2047 && x.fracField != 0

/-- Whether `x` is `+∞` or `-∞`, as `isinf` of `math.h` decides it: the largest exponent and the
fraction zero. -/
def isInf (x : Double) : Bool := x.expField == 2047 && x.fracField == 0

/-- Whether `x` is `0.0` or `-0.0`. -/
def isZero (x : Double) : Bool := x.bits &&& 0x7fffffffffffffff == 0

/-- Whether `x` is finite, as `isfinite` of `math.h` decides it: an exponent below the largest, so
neither an infinity nor a NaN. -/
def isFinite (x : Double) : Bool := x.expField != 2047

/-- The key of a double that is not a NaN in the order of the values: the bits without the sign
bit, negated when the sign bit is set, which increase with the value for doubles of either sign,
the infinities included, and are `0` for both zeros. -/
def orderValue (x : Double) : Int :=
  let a : Int := (x.bits &&& 0x7fffffffffffffff).toNat
  if x.signBit then -a else a

/-- `x < y` of the C language on doubles: false when either is a NaN, and otherwise the order of
the values, in which `-0.0` and `0.0` are equal. -/
def lt (x y : Double) : Bool := !x.isNaN && !y.isNaN && x.orderValue < y.orderValue

/-- `x <= y` of the C language on doubles: false when either is a NaN, and otherwise the order of
the values, in which `-0.0` and `0.0` are equal. -/
def le (x y : Double) : Bool := !x.isNaN && !y.isNaN && x.orderValue ≤ y.orderValue

/-- `x == y` of the C language on doubles: false when either is a NaN, and otherwise the equality
of the values, under which `-0.0` and `0.0` are equal. -/
def beq (x y : Double) : Bool := !x.isNaN && !y.isNaN && x.orderValue == y.orderValue

/-- The negation `-x` of the C language on a double: the sign bit flipped, also for a zero, an
infinity and a NaN. -/
def neg (x : Double) : Double := ⟨x.bits ^^^ 0x8000000000000000⟩

/-- `fabs` of `math.h`: the sign bit cleared. -/
def fabs (x : Double) : Double := ⟨x.bits &&& 0x7fffffffffffffff⟩

/-- The exact value `m 2 ^ e` of a finite double `x`, as the pair `(m, e)`: for a normal `x` the
significand `2 ^ 52 + f` of the fraction `f` with the exponent less `1075`, for a subnormal `x` or a
zero the fraction with `e = -1074`, and `m` negated when the sign bit is set (`m = 0` for both
zeros). Not meant for infinities and NaNs. -/
def toDyadic (x : Double) : Int × Int :=
  let (m, e) : Nat × Int :=
    if x.expField = 0 then (x.fracField, -1074) else (x.fracField + 2 ^ 52, x.expField - 1075)
  (if x.signBit then -(m : Int) else m, e)

/-- The exact value of a finite double `x` as a rational number, `m 2 ^ e` for the pair `(m, e)` of
`Ratpoints.Double.toDyadic`, as `mpq_set_d` of GMP sets it: `0` for both zeros. Not meant for
infinities and NaNs. -/
def toRat (x : Double) : Rat :=
  let (m, e) := x.toDyadic
  if 0 ≤ e then ((m * 2 ^ e.toNat : Int) : Rat) else mkRat m (2 ^ (-e).toNat)

/-- `m / 2 ^ k` rounded to the nearest integer, ties to even, and `m 2 ^ (-k)` for `k ≤ 0`. -/
def roundShift (m : Nat) (k : Int) : Nat :=
  if k ≤ 0 then m <<< (-k).toNat
  else
    let q := m >>> k.toNat
    let r := m % 2 ^ k.toNat
    let half := 2 ^ (k.toNat - 1)
    if half < r ∨ r = half ∧ q % 2 = 1 then q + 1 else q

/-- The double with the sign `-` for `neg` that IEEE 754 encodes by a significand `M < 2 ^ 53` and
the exponent `q` of its last place: a subnormal or a zero with the fraction `M` for `M < 2 ^ 52`
(whose last place is `2 ^ (-1074)`), an infinity when the exponent field `q + 1075` would reach
`2047`, and otherwise a normal double with the exponent field `q + 1075` and the fraction
`M - 2 ^ 52`. -/
def assemble (neg : Bool) (M : Nat) (q : Int) : Double :=
  let s : UInt64 := if neg then 0x8000000000000000 else 0
  if M < 2 ^ 52 then ⟨s ||| M.toUInt64⟩
  else if 2047 ≤ q + 1075 then ⟨s ||| 0x7ff0000000000000⟩
  else ⟨s ||| ((q + 1075).toNat.toUInt64 <<< 52) ||| (M - 2 ^ 52).toUInt64⟩

/-- The double with the sign `-` for `neg` of a rounded significand `M ≤ 2 ^ 53` and the exponent
`q` of its last place, the last step of `Ratpoints.Double.ofDyadic` and `Ratpoints.Double.ofRatio`:
the significand `2 ^ 53`, which rounding up can reach, carried into the next exponent as `2 ^ 52`,
then the bits of `Ratpoints.Double.assemble`. -/
def ofSignificand (neg : Bool) (M : Nat) (q : Int) : Double :=
  let (M, q) := if M = 2 ^ 53 then (2 ^ 52, q + 1) else (M, q)
  assemble neg M q

/-- The double nearest to `±m 2 ^ e`, the sign `-` for `neg`, with ties to even, as the operations
of IEEE 754 round their exact results in the rounding mode to nearest: a signed zero for `m = 0`;
otherwise the last place `2 ^ q` of the result, `q = max (E - 52) (-1074)` for the exponent `E` with
`2 ^ E ≤ m 2 ^ e < 2 ^ (E + 1)`; `M`, the value divided by `2 ^ q` and rounded, carried into the
next exponent at `2 ^ 53`; a subnormal or a zero below `2 ^ 52`; and an infinity beyond the largest
finite double (`Ratpoints.Double.ofSignificand`). The proofs show only that a finite result for
`m ≠ 0` is a faithful rounding: the value lies strictly between the neighbours of the result
(`Ratpoints.Double.lt_nextUp_and_nextDown_lt_ofDyadic`). -/
def ofDyadic (neg : Bool) (m : Nat) (e : Int) : Double :=
  if m = 0 then ⟨if neg then 0x8000000000000000 else 0⟩
  else
    let q : Int := max (m.log2 + e - 52) (-1074)
    ofSignificand neg (roundShift m (q - e)) q

/-- The double nearest to `±n / d` for `d ≠ 0`, the sign `-` for `neg`, with ties to even, as IEEE
754 rounds an exact result in the rounding mode to nearest: a signed zero for `n = 0`; otherwise the
exponent `E` with `2 ^ E ≤ n / d < 2 ^ (E + 1)`, which the lengths of `n` and `d` in bits fix up to
one, the last place `2 ^ q` of the result, `q = max (E - 52) (-1074)`, the quotient `n / (d 2 ^ q)`
rounded to the nearest integer `M` (`r` the remainder), carried into the next exponent at `2 ^ 53`,
a subnormal or a zero below `2 ^ 52`, and an infinity beyond the largest finite double
(`Ratpoints.Double.ofSignificand`). The proofs show only that a finite result for `n ≠ 0` and
`d ≠ 0` is a faithful rounding: the value lies strictly between the neighbours of the result
(`Ratpoints.Double.lt_nextUp_and_nextDown_lt_ofRatio`). -/
def ofRatio (neg : Bool) (n d : Nat) : Double :=
  if n = 0 then ⟨if neg then 0x8000000000000000 else 0⟩
  else
    let e : Int := (n.log2 : Int) - d.log2
    let atLeast : Bool := if 0 ≤ e then d * 2 ^ e.toNat ≤ n else d ≤ n * 2 ^ (-e).toNat
    let q : Int := max ((if atLeast then e else e - 1) - 52) (-1074)
    let (a, b) := if 0 ≤ q then (n, d * 2 ^ q.toNat) else (n * 2 ^ (-q).toNat, d)
    let r := a % b
    let M := if b < 2 * r ∨ 2 * r = b ∧ (a / b) % 2 = 1 then a / b + 1 else a / b
    ofSignificand neg M q

/-- The conversion `(double)n` of a `long` `n` to a double: the double nearest to `n`, ties to even,
as gcc converts it on the platforms of `ratpoints`, exact for `|n| ≤ 2 ^ 53`, and `±2 ^ 63` for
`n = ±(2 ^ 63 - 1)`. -/
def ofInt64 (n : Int64) : Double := ofDyadic (n < 0) n.toInt.natAbs 0

/-- The conversion `(long)x` of a finite double `x` with `|x| < 2 ^ 63` to a `long`: the value
truncated towards zero, as the C language defines it for the doubles whose truncation is a `long`
(for the others the conversion is undefined, and the value here is of no meaning). -/
def toInt64 (x : Double) : Int64 :=
  let (m, e) := x.toDyadic
  let a := if 0 ≤ e then m.natAbs <<< e.toNat else m.natAbs >>> (-e).toNat
  Int64.ofInt (if m < 0 then -(a : Int) else a)

/-- The conversion `(unsigned long)x` of a finite double `0 ≤ x < 2 ^ 64` to an `unsigned long`:
the value truncated towards zero, as the C language defines it for those doubles (for the others
the conversion is undefined, and the value here is of no meaning). -/
def toUInt64 (x : Double) : UInt64 :=
  let (m, e) := x.toDyadic
  (if 0 ≤ e then m.natAbs <<< e.toNat else m.natAbs >>> (-e).toNat).toUInt64

/-- `ldexp(x, n)` of `math.h`, `x 2 ^ n`: a zero, an infinity and a NaN as they are, as glibc
returns them, but for a signalling NaN, which glibc returns quieted (by `x + x`; `ratpoints` passes
it no NaN); otherwise the exact value of `x` times `2 ^ n` rounded to a double
(`Ratpoints.Double.ofDyadic`), which is exact unless it leaves the normal range, an infinity on
overflow and rounded to nearest in the subnormal range, as glibc computes it. -/
def ldexp (x : Double) (n : Int) : Double :=
  if x.isNaN || x.isInf || x.isZero then x
  else
    let (m, e) := x.toDyadic
    ofDyadic x.signBit m.natAbs (e + n)

/-- `frexp(x, &ex)` of `math.h`: the pair `(f, ex)` with `x = f 2 ^ ex` and `1/2 ≤ |f| < 1`, `f` of
the sign of `x`, for a finite `x ≠ 0`, also a subnormal one; `(x, 0)` for a zero, an infinity and a
NaN, as glibc returns them, but for a signalling NaN, which glibc returns quieted (by `x + x`;
`ratpoints` passes it no NaN). -/
def frexp (x : Double) : Double × Int :=
  if x.isNaN || x.isInf || x.isZero then (x, 0)
  else
    let (m, e) := x.toDyadic
    let l : Int := m.natAbs.log2 + 1
    (ofDyadic x.signBit m.natAbs (-l), l + e)

/-- `nextafter(x, HUGE_VAL)` of `math.h`: the least double above `x`; the least subnormal for both
zeros, `+∞` for `+∞` and the largest finite double, a NaN as it is (glibc returns a signalling NaN
quieted, by `x + y`; `ratpoints` passes it no NaN), and for a negative `x` the double towards zero,
`-0.0` above `-2 ^ (-1074)`. -/
def nextUp (x : Double) : Double :=
  if x.isNaN || x.bits == huge.bits then x
  else if x.isZero then ⟨1⟩
  else if x.signBit then ⟨x.bits - 1⟩
  else ⟨x.bits + 1⟩

/-- `nextafter(x, -HUGE_VAL)` of `math.h`: the greatest double below `x`; the least subnormal
negated for both zeros, `-∞` for `-∞` and the least finite double, a NaN as it is (glibc returns a
signalling NaN quieted, by `x + y`; `ratpoints` passes it no NaN), and for a positive `x` the double
towards zero, `0.0` below `2 ^ (-1074)`. -/
def nextDown (x : Double) : Double :=
  if x.isNaN || x.bits == huge.neg.bits then x
  else if x.isZero then ⟨0x8000000000000001⟩
  else if x.signBit then ⟨x.bits + 1⟩
  else ⟨x.bits - 1⟩

/-- What `printf` of glibc prints for the double `x` under the conversion `%.pf`, of which `%f` and
`%lf` are `%.6f`: the exact value of `x` rounded to `p` places after the point, ties to even, in
full however large it is, without the point for `p = 0`, after a `-` whenever the sign bit is set,
also for `-0.0` and for a negative value that rounds to `0`; `inf` for an infinity and `nan` for a
NaN, after a `-` when the sign bit is set. -/
def printFixed (p : Nat) (x : Double) : String :=
  let sign := if x.signBit then "-" else ""
  if x.isNaN then sign ++ "nan"
  else if x.isInf then sign ++ "inf"
  else
    let (m, e) := x.toDyadic
    let n := roundShift (m.natAbs * 10 ^ p) (-e)
    let f := toString (n % 10 ^ p)
    sign ++ toString (n / 10 ^ p) ++ if p = 0 then "" else "." ++ "".pushn '0' (p - f.length) ++ f

/-! ### Examples

The operations on the edge cases that matter (both zeros, the subnormals, the largest finite
doubles, the infinities, a NaN, `2 ^ 53` and `2 ^ 63` with their neighbours, ties of the rounding),
against what a C program compiled with gcc and linked with glibc on the platform of `ratpoints`
prints for them, as bits. -/

-- `(double)n`: exact up to `2 ^ 53`, ties to even above it, `±(2 ^ 63 - 1)` and `-2 ^ 63` to
-- `±2 ^ 63`, and the neighbours of `2 ^ 63 - 512`, the tie between the largest double below
-- `2 ^ 63` and `2 ^ 63`.
#guard ([(0, 0x0000000000000000), (1, 0x3ff0000000000000), (-1, 0xbff0000000000000),
    (3, 0x4008000000000000), (2 ^ 52, 0x4330000000000000), (2 ^ 53, 0x4340000000000000),
    (2 ^ 53 + 1, 0x4340000000000000), (2 ^ 53 + 2, 0x4340000000000001),
    (2 ^ 53 + 3, 0x4340000000000002), (-(2 ^ 53 + 1), 0xc340000000000000),
    (-(2 ^ 53 + 3), 0xc340000000000002), (2 ^ 62 + 2 ^ 9, 0x43d0000000000000),
    (2 ^ 62 + 2 ^ 10 + 2 ^ 9, 0x43d0000000000002), (2 ^ 62 + 2 ^ 9 + 1, 0x43d0000000000001),
    (2 ^ 63 - 1, 0x43e0000000000000), (-(2 ^ 63 - 1), 0xc3e0000000000000),
    (-2 ^ 63, 0xc3e0000000000000), (2 ^ 63 - 1025, 0x43dfffffffffffff),
    (2 ^ 63 - 512, 0x43e0000000000000), (2 ^ 63 - 513, 0x43dfffffffffffff),
    (2 ^ 63 - 514, 0x43dfffffffffffff), (123456789012345, 0x42dc12218377de40),
    (-987654321098765432, 0xc3ab69b4be93f169), (2 ^ 54 + 2, 0x4350000000000000),
    (2 ^ 54 + 6, 0x4350000000000002), (2 ^ 54 + 3, 0x4350000000000001)] :
    List (Int × UInt64)).all fun (n, b) ↦ (ofInt64 (Int64.ofInt n)).bits == b

-- `x < y`, `x <= y` and `x == y` for every pair of 21 doubles: for each `x`, the masks of the `y`
-- for which the comparison is true, bit `j` for the `j`-th double (so a NaN, the nineteenth, is
-- unordered, and `-0.0` equals `0.0`).
#guard
  let xs : List UInt64 := [0x0000000000000000, 0x8000000000000000, 0x0000000000000001,
    0x8000000000000001, 0x000fffffffffffff, 0x0010000000000000, 0x3ff0000000000000,
    0xbff0000000000000, 0x7fefffffffffffff, 0xffefffffffffffff, 0x7ff0000000000000,
    0xfff0000000000000, 0x43e0000000000000, 0x43dfffffffffffff, 0xc3e0000000000000,
    0x3fe8000000000000, 0x0008000000000000, 0x4340000000000001, 0x7ff8000000000000,
    0x3cb0000000000000, 0x000123456789abcd]
  let masks : List (Nat × Nat × Nat) := [(1815924, 1815927, 3), (1815924, 1815927, 3),
    (1815920, 1815924, 4), (1815927, 1815935, 8), (701792, 701808, 16), (701760, 701792, 32),
    (144640, 144704, 64), (1815935, 1816063, 128), (1024, 1280, 256), (1832447, 1832959, 512),
    (0, 1024, 1024), (1832959, 1835007, 2048), (1280, 5376, 4096), (5376, 13568, 8192),
    (1816063, 1832447, 16384), (144704, 177472, 32768), (701808, 767344, 65536),
    (13568, 144640, 131072), (0, 0, 0), (177472, 701760, 524288), (767344, 1815920, 1048576)]
  let mask (f : Double → Double → Bool) (x : UInt64) : Nat :=
    (xs.zipIdx.filter fun (y, _) ↦ f ⟨x⟩ ⟨y⟩).foldl (fun m (_, j) ↦ m + 2 ^ j) 0
  (xs.zip masks).all fun (x, l, e, q) ↦ mask lt x == l && mask le x == e && mask beq x == q

-- `-x` and `fabs(x)`.
#guard ([(0x0000000000000000, 0x8000000000000000, 0x0000000000000000),
    (0x8000000000000000, 0x0000000000000000, 0x0000000000000000),
    (0x0000000000000001, 0x8000000000000001, 0x0000000000000001),
    (0x8000000000000001, 0x0000000000000001, 0x0000000000000001),
    (0x000fffffffffffff, 0x800fffffffffffff, 0x000fffffffffffff),
    (0x7fefffffffffffff, 0xffefffffffffffff, 0x7fefffffffffffff),
    (0xffefffffffffffff, 0x7fefffffffffffff, 0x7fefffffffffffff),
    (0x7ff0000000000000, 0xfff0000000000000, 0x7ff0000000000000),
    (0xfff0000000000000, 0x7ff0000000000000, 0x7ff0000000000000),
    (0x43dfffffffffffff, 0xc3dfffffffffffff, 0x43dfffffffffffff),
    (0xc3e0000000000000, 0x43e0000000000000, 0x43e0000000000000),
    (0x7ff8000000000000, 0xfff8000000000000, 0x7ff8000000000000)] :
    List (UInt64 × UInt64 × UInt64)).all fun (x, n, f) ↦
  (neg ⟨x⟩).bits == n && (fabs ⟨x⟩).bits == f

-- `nextafter` towards `±HUGE_VAL` and `frexp`.
#guard ([(0x0000000000000000, 0x0000000000000001, 0x8000000000000001),
    (0x8000000000000000, 0x0000000000000001, 0x8000000000000001),
    (0x0000000000000001, 0x0000000000000002, 0x0000000000000000),
    (0x8000000000000001, 0x8000000000000000, 0x8000000000000002),
    (0x000fffffffffffff, 0x0010000000000000, 0x000ffffffffffffe),
    (0x7fefffffffffffff, 0x7ff0000000000000, 0x7feffffffffffffe),
    (0xffefffffffffffff, 0xffeffffffffffffe, 0xfff0000000000000),
    (0x7ff0000000000000, 0x7ff0000000000000, 0x7fefffffffffffff),
    (0xfff0000000000000, 0xffefffffffffffff, 0xfff0000000000000),
    (0x43dfffffffffffff, 0x43e0000000000000, 0x43dffffffffffffe),
    (0xc3e0000000000000, 0xc3dfffffffffffff, 0xc3e0000000000001),
    (0x7ff8000000000000, 0x7ff8000000000000, 0x7ff8000000000000)] :
    List (UInt64 × UInt64 × UInt64)).all fun (x, u, d) ↦
  (nextUp ⟨x⟩).bits == u && (nextDown ⟨x⟩).bits == d
#guard ([(0x0000000000000000, 0x0000000000000000, 0), (0x8000000000000000, 0x8000000000000000, 0),
    (0x0000000000000001, 0x3fe0000000000000, -1073),
    (0x8000000000000001, 0xbfe0000000000000, -1073),
    (0x000fffffffffffff, 0x3feffffffffffffe, -1022),
    (0x0010000000000000, 0x3fe0000000000000, -1021),
    (0x3ff0000000000000, 0x3fe0000000000000, 1), (0xbff0000000000000, 0xbfe0000000000000, 1),
    (0x7fefffffffffffff, 0x3fefffffffffffff, 1024), (0x43e0000000000000, 0x3fe0000000000000, 64),
    (0x43dfffffffffffff, 0x3fefffffffffffff, 63), (0x3fe8000000000000, 0x3fe8000000000000, 0),
    (0x0008000000000000, 0x3fe0000000000000, -1022), (0x4340000000000001, 0x3fe0000000000001, 54),
    (0x3cb0000000000000, 0x3fe0000000000000, -51),
    (0x000123456789abcd, 0x3fe23456789abcd0, -1025)] :
    List (UInt64 × UInt64 × Int)).all fun (x, f, e) ↦
  (frexp ⟨x⟩).1.bits == f && (frexp ⟨x⟩).2 == e

-- `ldexp`: exact, rounded into the subnormals (ties to even), overflow to `+∞`, and the doubles
-- that `exact_end` scales, `ldexp(f, 53)` for `1/2 ≤ f < 1`.
#guard ([(0x3ff0000000000000, 53, 0x4340000000000000), (0x3ff0000000000000, -1074, 1),
    (0x3ff0000000000000, -1075, 0), (0x3ff8000000000000, -1075, 1), (0x3ff0000000000000, -1076, 0),
    (0x3ff8000000000000, -1074, 2), (0x4004000000000000, -1074, 2), (0x400c000000000000, -1074, 4),
    (0x3ff0000000000000, 1023, 0x7fe0000000000000), (0x3ff0000000000000, 1024, 0x7ff0000000000000),
    (0xc340000000000000, -55, 0xbfd0000000000000), (0x43e0000000000000, 0, 0x43e0000000000000),
    (0xc3e0000000000000, -3, 0xc3b0000000000000), (0x4340000000000000, -60, 0x3f80000000000000),
    (0x0000000000000001, 1074, 0x3ff0000000000000), (0x0000000000000003, -1, 2),
    (0x0000000000000003, 1, 6), (0x8000000000000000, 5, 0x8000000000000000),
    (0x7ff0000000000000, -5, 0x7ff0000000000000), (0x3fe0000000000000, 53, 0x4330000000000000),
    (0x3fefffffffffffff, 53, 0x433fffffffffffff), (0x433fffffffffffff, -30, 0x415fffffffffffff),
    (0xc32fffffffffffff, -1100, 0x8000000004000000)] :
    List (UInt64 × Int × UInt64)).all fun (x, n, y) ↦ (ldexp ⟨x⟩ n).bits == y

-- `(long)x` and `(unsigned long)x`, truncated towards zero.
#guard ([(0x3ff0000000000000, 1), (0x3fe0000000000000, 0), (0xbfe0000000000000, 0),
    (0x4340000000000000, 9007199254740992), (0x433fffffffffffff, 9007199254740991),
    (0x43dfffffffffffff, 9223372036854774784), (0xc3dfffffffffffff, -9223372036854774784),
    (0x400c000000000000, 3), (0xc00c000000000000, -3), (0x0000000000000001, 0),
    (0x8000000000000000, 0), (0xc3e0000000000000, -9223372036854775808)] :
    List (UInt64 × Int)).all fun (x, n) ↦ (toInt64 ⟨x⟩).toInt == n
#guard ([(0x3ff0000000000000, 1), (0x4340000000000000, 9007199254740992),
    (0x433fffffffffffff, 9007199254740991), (0x43e0000000000000, 9223372036854775808),
    (0x43efffffffffffff, 18446744073709549568), (0x3fefffffffffffff, 0),
    (0x4330000000000000, 4503599627370496)] :
    List (UInt64 × Nat)).all fun (x, n) ↦ (toUInt64 ⟨x⟩).toNat == n

-- `printf` of glibc under `%.0f`, `%.1f` and `%.2f`: ties to even at the last place (`0.5`, `1.5`,
-- `2.5`, `0.25`, `0.75`, `0.125`, `0.375`), `-` on the sign bit also for `-0.0` and for negative
-- values that round to `0`, the double nearest to `0.715` and to `1.005`, which lie below the ties,
-- a large value in full, and no point for `%.0f`.
#guard ([(0x3fe0000000000000, "0", "0.5", "0.50"), (0x3ff8000000000000, "2", "1.5", "1.50"),
    (0x4004000000000000, "2", "2.5", "2.50"), (0xbfe0000000000000, "-0", "-0.5", "-0.50"),
    (0x3fd0000000000000, "0", "0.2", "0.25"), (0x3fe8000000000000, "1", "0.8", "0.75"),
    (0x3fc0000000000000, "0", "0.1", "0.12"), (0x3fd8000000000000, "0", "0.4", "0.38"),
    (0xbfa47ae147ae147b, "-0", "-0.0", "-0.04"), (0x3fe6e147ae147ae1, "1", "0.7", "0.71"),
    (0x3ff0147ae147ae14, "1", "1.0", "1.00"), (0x4050000000000000, "64", "64.0", "64.00"),
    (0x4450000000000000, "1180591620717411303424", "1180591620717411303424.0",
      "1180591620717411303424.00"), (0xfff0000000000000, "-inf", "-inf", "-inf")] :
    List (UInt64 × String × String × String)).all fun (x, s0, s1, s2) ↦
  (Double.mk x).printFixed 0 == s0 && (Double.mk x).printFixed 1 == s1 &&
    (Double.mk x).printFixed 2 == s2

end Double

end Ratpoints

end
