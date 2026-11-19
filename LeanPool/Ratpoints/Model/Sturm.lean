/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Model.Double

-- The `#guard` examples run code of the imported module at compile time.
meta import LeanPool.Ratpoints.Model.Double

/-!
# The Sturm step

The Sturm step of `ratpoints`, `_ratpoints_compute_sturm` of `sturm.c`, which restricts the search
to the intervals where the polynomial `f` may be `≥ 0`, computed in integers and on the doubles of
the C code as `sturm.c` computes it. First the remainder chain of `f` and its derivative `f'`, row
by row and with its loops (`Ratpoints.Sturm.chain`): a remainder is zero exactly when `f` has a
repeated factor; the chain is `none` then, and `ratpoints` refuses the form as not squarefree, as
`Ratpoints.findPoints` does with the Sturm step on. Then the numbers of sign changes of the chain at
`-∞` and `+∞` from the leading coefficients (`Ratpoints.Sturm.countsAtInfinity`), with the exit
when `f` has no real root and is negative; the bisection of the real line from `[-∞, +∞]`, which
drops an interval without a root on which `f` is negative, keeps one without a root on which it is
positive and one at the depth of the step, and splits the others at their midpoint
(`Ratpoints.Sturm.midpoint`), where it evaluates the chain (`Ratpoints.Sturm.evalSign`,
`Ratpoints.Sturm.signsAt`), the left half first (`Ratpoints.Sturm.iterate`); the kept intervals,
with dyadic ends `n / 2 ^ e` converted to doubles and an interval that begins where the last one
ends joined to it (`Ratpoints.Sturm.addInterval`); and their intersection with the search intervals
of the caller (`Ratpoints.Sturm.intersect`). The whole step is `Ratpoints.Sturm.computeSturm`,
which the search calls through `Ratpoints.sturmRegion`.

## Main definitions

* `Ratpoints.Sturm.reduce`: one reduction of a remainder by the row before it, which cancels its
  leading coefficient.
* `Ratpoints.Sturm.chain`: the remainder chain of `f` and `f'`, or `none` when a remainder is zero.
* `Ratpoints.Sturm.evalSign`, `Ratpoints.Sturm.signsAt`: the sign of a row at a dyadic number, and
  the signs of `f` and `f'` and the number of sign changes of the chain there.
* `Ratpoints.Sturm.countsAtInfinity`: the numbers of sign changes of the chain at `±∞`.
* `Ratpoints.Sturm.midpoint`, `Ratpoints.Sturm.addInterval`, `Ratpoints.Sturm.iterate`: the
  bisection.
* `Ratpoints.Sturm.meet`, `Ratpoints.Sturm.intersect`: the intersection with the caller's
  intervals.
* `Ratpoints.Sturm.computeSturm`: the Sturm step.
-/

@[expose] public section

namespace Ratpoints

namespace Sturm

/-- One reduction of `t` by `s`, for `deg t ≥ deg s`, each given by the array of its coefficients up
to its degree, constant term first: `u t - v X^(deg t - deg s) s`, where `u` and `v` are the leading
coefficients of `s` and `t` divided by their positive gcd and signed so that `u > 0`; the leading
coefficient of the result is `0`. -/
def reduce (s t : Array Int) : Array Int :=
  let d1 := s.size - 1
  let d2 := t.size - 1
  let g : Int := Int.gcd s.back! t.back!
  let u0 := s.back! / g
  let v0 := t.back! / g
  let u := if u0 < 0 then -u0 else u0
  let v := if u0 < 0 then -v0 else v0
  (Array.range (d2 + 1)).map fun n ↦
    if n < d2 - d1 then u * t[n]! else u * t[n]! - v * s[n - (d2 - d1)]!

/-- The remainder chain of the polynomial `f` of degree `d ≥ 1` with the coefficients
`c₀, …, c_d`, the entries of `c`, and `c_d ≠ 0`, in rows of integers: `s₀ = f`, `s₁ = f'`, and for
`k = 2, …, d` the row `s_k` from the remainder `t` of `s_(k-2)` by `s_(k-1)`. Starting from
`t = s_(k-2)`, while the degree of `t` is at least that of `s_(k-1)`, `t` is reduced by `s_(k-1)`
(`Ratpoints.Sturm.reduce`) and its zero leading coefficients are dropped; the chain is `none` when
`t` becomes zero, which happens exactly when `f` has a repeated factor
(`Ratpoints.Sturm.run_chain_eq_none_iff`). Otherwise `s_k` is `-t` divided by the gcd of its
coefficients, whose loop stops when the gcd is `1`, and the chain ends when `s_k` is constant. Each
row is the array of its coefficients up to its degree, constant term first; for `d = 1` the loop
over `k` does not run, and the chain is `f, f'`.

C: `sturm.c:99-163`

Deviation: the rows as arrays of their coefficients up to their degree, for the table of `(d + 1)^2`
GMP integers and the array of degrees, with no `mpz_init` and `mpz_clear` (a chain has at most
`d + 1` rows, `Ratpoints.Sturm.IsChain.size_le`, and its row `k + 1` at most `d - k` entries,
`Ratpoints.Sturm.IsChain.size_getElem!_add_one_add_le`): an array has one entry more than the degree
of its row, and a remainder that becomes zero is the empty array, where the degree in the C code
reaches `-1`; a reduction step drops the leading coefficient, which it makes `0`, where the C code
lowers the degree; the rows are handed back, and `none` for the return of `-1`, where
`_ratpoints_compute_sturm` keeps them in its table for the rest of the Sturm step
(`Ratpoints.Sturm.computeSturm`), and the index of the last row, which the C code leaves in `k` and
sets to `d` after the loop for `d = 1`, is the size of the array less one; a list of integers for
the array of GMP integers of the coefficients, local values for the scratch integers `work[0]`,
`work[1]` and `work[2]`, and Lean's `/` for `mpz_fdiv_q`, which agree on the divisions of the chain,
all exact. -/
def chain (c : List Int) (d : Nat) : Id (Option (Array (Array Int))) := do
  let f : Array Int := (Array.range (d + 1)).map (c.getD · 0)
  let df : Array Int := (Array.range d).map fun (n : Nat) ↦ (n + 1 : Int) * c.getD (n + 1) 0
  let mut rows := #[f, df]
  for k in [2:d + 1] do
    let s := rows[k - 1]!
    let mut t := rows[k - 2]!
    while s.size ≤ t.size do
      t := (reduce s t).pop
      while t.back? == some 0 do t := t.pop
      if t.size = 0 then return none
    t := t.map (- ·)
    let mut g := 0
    for a in t do
      g := Nat.gcd g a.natAbs
      if g = 1 then break
    if g ≠ 1 then t := t.map (· / (g : Int))
    rows := rows.push t
    if t.size = 1 then break
  return some rows

/-- The sign `-1`, `0` or `1` of the value at `num / 2 ^ denexp` of the polynomial whose
coefficients, constant term first, are the entries of `row`, as `eval_sign` computes it: by Horner's
rule in integers, from the leading coefficient `w = c_deg`, for `n = deg - 1, …, 0` in turn
`w = w num + c_n 2 ^ e` with `e = denexp, 2 denexp, …`, so that `w` is `2 ^ (deg denexp)` times the
value, `deg` the size of `row` less one.

C: `sturm.c:67-84`

Deviation: the row as an array of integers, for the GMP integers `cofs` and the `long` `degree`,
which is the size of the array less one; integers for the GMP integers `work[0]` and `work[1]`, the
multiplication by a power of 2 for `mpz_mul_2exp`, and `Int.sign` for `mpz_sgn`; `Int64` for the
`long`s `num`, `denexp` and `e`; the steps counted up from `0` to `deg - 1`, for the index `n` that
counts down; no scratch integers of the arguments. -/
def evalSign (row : Array Int) (num denexp : Int64) : Id Int := do
  let deg := row.size - 1
  let mut w := row[deg]!
  let mut e := denexp
  for i in [0:deg] do
    w := w * num.toInt + row[deg - 1 - i]! * 2 ^ e.toInt.toNat
    e := e + denexp
  return w.sign

/-- The numbers of sign changes of the rows `0, …, k` of the chain `rows` at `+∞` and at `-∞`, the
pair `(count1, count2)`, from the signs of their leading coefficients: two neighbouring rows count
at `+∞` when their leading coefficients have different signs, and at `-∞` when they do after the
sign of each row of odd degree is flipped.

C: `sturm.c:165-175`

Deviation: natural numbers for the `long` counts, which stay at most `k`; the rows as arrays, their
degrees the sizes less one, for the arrays `sturm` and `sturm_degs`, and `Int.sign` for `mpz_sgn`;
the counts returned, for the locals of `_ratpoints_compute_sturm`. -/
def countsAtInfinity (rows : Array (Array Int)) (k : Nat) : Id (Nat × Nat) := do
  let mut count1 := 0
  let mut count2 := 0
  for n in [0:k] do
    let d1 := rows[n]!.size - 1
    let d2 := rows[n + 1]!.size - 1
    let mut s1 := rows[n]![d1]!.sign
    let mut s2 := rows[n + 1]![d2]!.sign
    if s1 ≠ s2 then count1 := count1 + 1
    if d1 % 2 = 1 then s1 := -s1
    if d2 % 2 = 1 then s2 := -s2
    if s1 ≠ s2 then count2 := count2 + 1
  return (count1, count2)

/-- `LONG_MAX = 2 ^ 63 - 1`, as `_ratpoints_compute_sturm` computes it, the `unsigned long` `-1`
shifted right by one bit: the numerator of the end at `+∞` of the bisection, and its negation that
of the end at `-∞`; converted to doubles, they become `±2 ^ 63`, beyond every `x = a / b` with
`|a| ≤ LONG_MAX`.

C: `sturm.c:191-192`

Deviation: one constant for the two locals `max` and `min = -max`. -/
def longMax : Int64 := ((~~~0 : UInt64) >>> 1).toInt64

/-- The point `nm / 2 ^ dem` at which the bisection splits the interval from `nl / 2 ^ del` to
`nr / 2 ^ der`: `0` for `[-∞, +∞]`; for `[-∞, nr]` the point `-1` if `nr = 0` and else `2 nr`, and
for `[nl, +∞]` the point `1` if `nl = 0` and else `2 nl`, both with `dem = 0` (the ends at infinity
are `∓Ratpoints.Sturm.longMax`, with the exponent `0`); for finite ends with `del = der`, which are
then both `0`, the half of `nl + nr`, with `dem = 0` when the sum is even and `dem = 1` otherwise;
and else the sum of the ends over the larger denominator, divided by `2`, so with the larger
exponent plus `1`.

C: `sturm.c:234-251`

Deviation: the point returned as a pair, for the locals `nm` and `dem` of `iterate`; `Int64` for
the `long`s, `>>>` on `Int64` the arithmetic shift of the C code; the arithmetic of `Int64`
wrapping where that of the `long`s overflows, which it does not up to the depth `55` at which the
search clamps the step, where every finite end is `n / 2 ^ e` with `|n| ≤ 2 ^ 53`. -/
def midpoint (nl nr del der : Int64) : Int64 × Int64 :=
  if nl == -longMax then
    if nr == longMax then (0, 0) else (if nr == 0 then -1 else 2 * nr, 0)
  else if nr == longMax then (if nl == 0 then 1 else 2 * nl, 0)
  else if del == der then
    if (nl + nr) &&& 1 == 0 then ((nl + nr) >>> 1, 0) else (nl + nr, 1)
  else if der < del then (nl + nr * (1 <<< (del - der)), del + 1)
  else (nl * (1 <<< (der - del)) + nr, der + 1)

/-- The signs `s0` and `s1` of `f` and `f'` at `nm / 2 ^ dem` (`Ratpoints.Sturm.evalSign`) and the
number `cmid` of sign changes of the rows `0, …, k` of the chain `rows` there, zeros skipped: the
first two rows count when their signs are opposite; then the sign `s` of the last row that is not
zero, `s0` when `s1 = 0`, and each further row counts when its sign is `-s`, and replaces `s` when
it is not zero.

C: `sturm.c:252-260`

Deviation: a function of its own for the evaluation of the chain at the midpoint in `iterate`, the
signs and the count returned, for its locals `s0`, `s1` and `cmid`; integers for the `long` signs
and a natural number for the `long` count; the rows as arrays, for the arrays `sturm` and
`sturm_degs`. -/
def signsAt (rows : Array (Array Int)) (k : Nat) (nm dem : Int64) : Id (Int × Int × Nat) := do
  let s0 ← evalSign rows[0]! nm dem
  let s1 ← evalSign rows[1]! nm dem
  let mut cmid := if s0 * s1 = -1 then 1 else 0
  let mut s := if s1 = 0 then s0 else s1
  for n in [2:k + 1] do
    let s2 ← evalSign rows[n]! nm dem
    if s2 = -s then
      cmid := cmid + 1
      s := s2
    else if s2 ≠ 0 then s := s2
  return (s0, s1, cmid)

/-- The interval from `nl / 2 ^ del` to `nr / 2 ^ der` added to the intervals `iv` that the
bisection keeps: its ends converted to doubles, `ldexp((double)n, -e)` (`Ratpoints.Double.ofInt64`,
`Ratpoints.Double.ldexp`), which is exact up to the depth `55` and gives `±2 ^ 63` for the ends at
infinity; the interval appended, or, when the last interval kept ends at its lower end (`==` of the
doubles, `Ratpoints.Double.beq`), that interval extended to its upper end.

C: `sturm.c:209-227`

Deviation: a function of its own for the branch of `iterate` that keeps an interval; the intervals
kept as an array, passed and returned, for the array `ivlocal` on the stack and the pointer `iptr`
of `_ratpoints_compute_sturm`, which `iterate` reaches as a nested function of gcc, with no bound
`1 + ⌊degree / 2⌋` on their number, the size of `ivlocal`, which the C code relies on and which
holds assuming Sturm's theorem (`Ratpoints.Sturm.size_run_iterate_le_of_chain_eq_some`); the doubles
as their bits (`Ratpoints.Double`); `Int64` for the `long`s, converted to integers for the `int`
casts of the exponents. -/
def addInterval (iv : Array (Double × Double)) (nl nr del der : Int64) : Array (Double × Double) :=
  let l := (Double.ofInt64 nl).ldexp (-del.toInt)
  let u := (Double.ofInt64 nr).ldexp (-der.toInt)
  match iv.back? with
  | some (lo, up) => if up.beq l then iv.pop.push (lo, u) else iv.push (l, u)
  | none => iv.push (l, u)

/-- The bisection of `_ratpoints_compute_sturm`, the nested function `iterate`, on the interval from
`nl / 2 ^ del` to `nr / 2 ^ der`, an end at infinity `∓Ratpoints.Sturm.longMax` with the exponent
`0`, with the numbers `cleft` and `cright` of sign changes of the chain `rows` (index of the last
row `k`) at its ends, as the step hands them on, and the signs `sl` and `sr` of `f` just inside its
ends, at the depth `depth`, adding the intervals it keeps to `iv`: an interval with `cleft = cright`
and `sl < 0`, without a root of `f` and with `f < 0` on it, is dropped; one with `cleft = cright`
and `sl > 0`, or at the depth `iter`, is kept (`Ratpoints.Sturm.addInterval`); and any other is
split at its midpoint `m` (`Ratpoints.Sturm.midpoint`), where the chain is evaluated
(`Ratpoints.Sturm.signsAt`), and its left half bisected before its right half, the count at `m` and
the sign of `f` at `m` handed to both halves, and when `m` is a root of `f`, the count plus `1` and
`-f'(m)` to the left half and the sign of `f'(m)` to the right half, the count and the sign just
left and just right of the simple root `m`.

C: `sturm.c:197-208`, `sturm.c:228-233`, `sturm.c:261-267`

Deviation: a recursive function of its own, for the nested function of gcc, with the intervals kept
passed and returned (`Ratpoints.Sturm.addInterval`), for the array `ivlocal` and the pointer `iptr`
that it reaches, and the chain, the index of its last row and the depth of the step as arguments,
for the arrays `sturm` and `sturm_degs`, `k` and `iter` that it reaches; natural numbers for the
`long` counts, depths and the `long` `iter`, which is from `0` to `55` (the search clamps it,
`find_points.c:4682`), integers for the `long` signs, and `Int64` for the other `long`s; the
recursion ends since the depth grows towards `iter`. -/
def iterate (rows : Array (Array Int)) (k iter : Nat) (nl nr del der : Int64) (cleft cright : Nat)
    (sl sr : Int) (depth : Nat) (iv : Array (Double × Double)) : Id (Array (Double × Double)) :=
  if cleft = cright ∧ sl < 0 then pure iv
  else if _h : cleft = cright ∧ 0 < sl ∨ iter ≤ depth then pure (addInterval iv nl nr del der)
  else do
    let (nm, dem) := midpoint nl nr del der
    let (s0, s1, cmid) ← signsAt rows k nm dem
    let iv ← iterate rows k iter nl nm del dem cleft (if s0 = 0 then cmid + 1 else cmid) sl
      (if s0 = 0 then -s1 else s0) (depth + 1) iv
    iterate rows k iter nm nr dem der cmid cright (if s0 = 0 then s1 else s0) sr (depth + 1) iv
termination_by iter - depth
decreasing_by all_goals lia

/-- One step of the intersection of the interval `a` that the bisection keeps with the interval `b`
of the caller, both closed, as the loop of `_ratpoints_compute_sturm` makes it: the interval it
notes, if any, and whether it goes on with the next interval kept (`true`) or the next interval of
the caller (`false`), the one that ends first. If `a` begins first (`a.low ≤ b.low`): `a` is
forgotten if it ends before `b` begins, and otherwise `[b.low, a.up]` is noted with the next `a` if
`a.up ≤ b.up`, and `b` with the next `b` otherwise; symmetrically if `b` begins first. The ends are
compared as doubles (`Ratpoints.Double.le`, `Ratpoints.Double.lt`) and copied, so that a `-0.0` of
the caller can stay.

C: `sturm.c:289-322`

Deviation: a function of its own for the body of the loop, the interval noted and the cursor to
move returned, for the write into `ivlist[n]` and the increments of `n`, `n1` and `n2`. -/
def meet (a b : Double × Double) : Option (Double × Double) × Bool :=
  if a.1.le b.1 then
    if a.2.lt b.1 then (none, true)
    else if a.2.le b.2 then (some (b.1, a.2), true)
    else (some b, false)
  else
    if b.2.lt a.1 then (none, false)
    else if b.2.le a.2 then (some (a.1, b.2), false)
    else (some a, true)

/-- The intersection of the intervals `loc` that the bisection keeps with the intervals `ivs` of the
caller, both increasing and disjoint, by the loop of `_ratpoints_compute_sturm`: from the first of
each, while both lists have one left, a step (`Ratpoints.Sturm.meet`) notes their intersection, if
they meet, and goes on with the next interval of the list whose interval ends first. The noted
intervals may be degenerate, `[a, a]`.

C: `sturm.c:276`, `sturm.c:285-288`, `sturm.c:323`, `sturm.c:325`

Deviation: the intervals of the caller read from the array it gives, where the C code reads them
from a copy on the heap (lines 274-275, 286) and writes the intersection over them; the intersection
returned as a new array, with no bound on its length, for the writes into `ivlist`, the caller's
array, which must have room for `1 + ⌊degree / 2⌋` intervals more than it holds (lines 52-53), as
the C code relies on and as suffices assuming Sturm's theorem
(`Ratpoints.Sturm.size_run_computeSturm_le`), and for the number `num_inter` of the arguments that
it sets; natural numbers for the `long` indices. -/
def intersect (loc ivs : Array (Double × Double)) : Id (Array (Double × Double)) := do
  let mut n1 := 0
  let mut n2 := 0
  let mut out := #[]
  while n1 < loc.size ∧ n2 < ivs.size do
    let (note, first) := meet loc[n1]! ivs[n2]!
    if let some v := note then out := out.push v
    if first then n1 := n1 + 1 else n2 := n2 + 1
  return out

/-- The Sturm step `_ratpoints_compute_sturm` on the polynomial `f` of degree `d ≥ 1` with the
coefficients `c₀, …, c_d`, the entries of `c`, and `c_d ≠ 0`, to the depth `iter`, for the search
intervals `ivlist` of the caller, increasing and disjoint: none when the remainder chain is none
(`Ratpoints.Sturm.chain`), for a polynomial with a repeated factor; the empty array when the chain
has as many sign changes at `-∞` as at `+∞` (`Ratpoints.Sturm.countsAtInfinity`), so that `f` has no
real root, and `c₀ < 0`, so that `f < 0` everywhere; and otherwise the intervals that the bisection
keeps from `[-∞, +∞]` (`Ratpoints.Sturm.iterate`, with the counts at `∓∞` at its ends and the sign
of `c_d`, negated at `-∞` for odd `d`, as the signs just inside them) intersected with `ivlist`
(`Ratpoints.Sturm.intersect`), which is empty when they do not meet.

C: `sturm.c:86-97`, `sturm.c:177-190`, `sturm.c:193-194`, `sturm.c:269-273`, `sturm.c:326-332`

Deviation: the coefficients, the degree, the depth and the search intervals as arguments, for the
fields `cof`, `degree`, `sturm`, `domain` and `num_inter` of the arguments; natural numbers for the
`long`s `degree` and `iter`, which is from `0` to `55` (the search clamps it,
`find_points.c:4682`); the result as an option of an array, for the `long` that the C code returns
and the intervals it writes into `domain` with their number `num_inter`: none for `-1`, the empty
array for `0`, with `num_inter = 0`, and else the intervals, their number the return value; the
table of the chain made by `Ratpoints.Sturm.chain`, whose rows the step reads, for the table on the
stack with the degrees, which `_ratpoints_compute_sturm` fills itself, the index of the last row
the size of the chain less one, for the `k` of line 163; the array of the intervals kept made by
`Ratpoints.Sturm.iterate`, for the array `ivlocal` on the stack of `1 + ⌊degree / 2⌋` intervals,
which suffice assuming Sturm's theorem (`Ratpoints.Sturm.size_run_iterate_le_of_chain_eq_some`);
integers for the GMP integers and `Int.sign` for `mpz_sgn`; no `mpz_init` and `mpz_clear`, no copy
of the caller's intervals on the heap and no failure for lack of memory (`RATPOINTS_NO_MEMORY`),
which the model cannot meet. -/
def computeSturm (c : List Int) (d iter : Nat) (ivlist : Array (Double × Double)) :
    Id (Option (Array (Double × Double))) := do
  let some rows ← chain c d | return none
  let k := rows.size - 1
  let (count1, count2) ← countsAtInfinity rows k
  if count2 = count1 ∧ c.getD 0 0 < 0 then return some #[]
  let slcf := (c.getD d 0).sign
  let ivlocal ← iterate rows k iter (-longMax) longMax 0 0 count2 count1
    (if d % 2 = 1 then -slcf else slcf) slcf 0 #[]
  return some (← intersect ivlocal ivlist)

/-! ### Examples -/

-- The rows of the chain against those that the C code at the pinned commit computes, printed by a
-- build of it instrumented to write out its table of the chain: for `3 + 2x` and
-- `1 + 2x + 3x ^ 2`; for `x ^ 3 - 2`, whose derivative has zero coefficients below its degree; for
-- `x ^ 12 + 1`, whose first remainder drops eleven zero coefficients after one reduction; for
-- polynomials of degree 6 and 12 with small coefficients; and for a polynomial of degree 4 with
-- coefficients of 70 bits.
#guard Id.run (chain [3, 2] 1) == some #[#[3, 2], #[2]]
#guard Id.run (chain [1, 2, 3] 2) == some #[#[1, 2, 3], #[2, 6], #[-1]]
#guard Id.run (chain [-2, 0, 0, 1] 3) == some #[#[-2, 0, 0, 1], #[0, 0, 3], #[1]]
#guard Id.run (chain [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] 12) ==
  some #[#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], #[-1]]
#guard Id.run (chain [1, -3, 0, 5, 2, -1, 4] 6) ==
  some #[#[1, -3, 0, 5, 2, -1, 4], #[-3, 0, 15, 8, -5, 24], #[-141, 360, -15, -368, -91],
    #[-8921, 25356, -7290, -23966], #[496649, -1172729, 269088], #[-49748239, 105235135], #[-1]]
#guard Id.run (chain [2, -1, 3, 0, -4, 1, 1, -2, 5, 0, 3, -1, 2] 12) ==
  some #[#[2, -1, 3, 0, -4, 1, 1, -2, 5, 0, 3, -1, 2],
    #[-1, 6, 0, -16, 5, 6, -14, 40, 0, 30, -11, 24],
    #[-575, 258, -720, 16, 763, -174, -130, 200, -480, -30, -133],
    #[-4297, 7960, -8317, 9084, 5299, -10144, 1803, 500, -5855, 3250],
    #[111239, -88670, 129479, -51258, -188013, 95378, 47239, -37650, 112885],
    #[-2439876, -6091220, 1760054, -19241828, 7067107, 4222068, -6355356, 14786680],
    #[-2424273052, 1406241100, -3746621942, 1084215784, 993254009, -821932394, -422045132],
    #[-130006268140, 135659934684, -236634150598, 156944360512, 24554040017, -70048221478],
    #[68783562254788, -34292889600876, 141878557171874, -37126415186292, 32209855661673],
    #[176570853748085, -3971981398746906, 1122760637623987, -7060821883560798],
    #[-29402021058230050567, 6696486453425578104, -51323577542404194557],
    #[-358926259923835158391, -582835008182379573626], #[1]]
#guard Id.run (chain [1150092013148293430274, -917191792855797489172, 1076517816789853128035,
    -1112533756463107743172, -159651315419584027538] 4) ==
  some #[#[1150092013148293430274, -917191792855797489172, 1076517816789853128035,
      -1112533756463107743172, -159651315419584027538],
    #[-917191792855797489172, 2153035633579706256070, -3337601269389323229516,
      -638605261678336110152],
    #[-494778259343239271161457560331419626137522, 519061916985381776446645105152951960484559,
      -636016745249336385621049668351111547060924],
    #[-1320514644362970048267102006596489210639285984427475928620543058408386120279245622586,
      316321408849073697612788777530870776056936461666231844513276181529277582337567078771], #[1]]

-- The chain is `none`, as in the C code, for `(x + 1) ^ 2` and for
-- `(3x ^ 2 + x - 5) ^ 2 (2x ^ 3 - x + 7)`, whose remainder is zero after six rows.
#guard (Id.run (chain [1, 2, 1] 2)).isNone
#guard (Id.run (chain [175, -95, -193, 121, 37, -67, 12, 18] 7)).isNone

-- The sign of a row at `num / 2 ^ denexp` against `eval_sign` of the C code at the pinned commit,
-- called by a C program that includes `sturm.c`: for each row, constant term first, the points
-- `(num, denexp)` with their signs; `x ^ 2 - 2` near `√2` and at the exponent 55,
-- `(2 x - 1) (4 x + 3) (x - 5)` at its roots and elsewhere, `x ^ 4 - 5 x ^ 2 + 1`, a constant, and
-- coefficients of 70 bits.
#guard
  ([([-2, 0, 1], [(3, 1, 1), (1, 0, -1), (-3, 1, 1), (0, 0, -1), (181, 7, -1), (363, 8, 1),
      (-363, 8, 1), (9007199254740991, 55, -1)]),
    ([15, -13, -38, 8], [(1, 1, 0), (-3, 2, 0), (5, 0, 0), (1, 0, -1), (-1, 0, -1), (0, 0, 1),
      (-7, 3, -1), (41, 3, 1)]),
    ([1, 0, -5, 0, 1], [(-9, 2, 1), (-1, 1, -1), (1, 1, -1), (9, 2, 1), (-4097, 12, -1)]),
    ([-1], [(5, 3, -1)]),
    ([123456789012345678901, -98765432109876543210, 5, 7, -1000000000000000000],
      [(-5, 0, -1), (79, 6, -1), (-321, 6, -1), (1, 0, 1)])] :
      List (List Int × List (Int64 × Int64 × Int))).all fun (row, pts) ↦
    pts.all fun (num, denexp, s) ↦ Id.run (evalSign row.toArray num denexp) == s

-- The numbers of sign changes of the chain at `+∞` and at `-∞` against those of the Sturm sequence
-- of `f` and `f'`, computed exactly over the rationals, their difference the number of real roots
-- of `f`: `x ^ 3 - 2`, `x ^ 4 - 5 x ^ 2 + 1`, `x ^ 2 + x + 1`, `-x ^ 4 - 1`,
-- `(2 x - 1) (4 x + 3) (x - 5)`, `3 + 2 x` and the polynomial of degree 12 of the chain above.
#guard
  ([([-2, 0, 0, 1], (0, 1)), ([1, 0, -5, 0, 1], (0, 4)), ([1, 1, 1], (1, 1)),
    ([-1, 0, 0, 0, -1], (1, 1)), ([15, -13, -38, 8], (0, 3)), ([3, 2], (0, 1)),
    ([2, -1, 3, 0, -4, 1, 1, -2, 5, 0, 3, -1, 2], (6, 6))] : List (List Int × Nat × Nat)).all
    fun (c, r) ↦ match Id.run (chain c (c.length - 1)) with
      | some rows => Id.run (countsAtInfinity rows (rows.size - 1)) == r
      | none => false

-- The signs of `f` and `f'` and the count of the chain at `nm / 2 ^ dem` against the signs of `f`
-- and `f'` and the number of sign changes of the Sturm sequence of `f` and `f'` there, zeros
-- skipped, computed exactly over the rationals: for `(2 x - 1) (4 x + 3) (x - 5)` at `0`, `-1` and
-- `6` and at its roots `1 / 2`, `-3 / 4` and `5`, and for `x ^ 3 - x` at its root `0`, at `1 / 2`
-- and at `-3 / 2`.
#guard
  ([([15, -13, -38, 8], [(0, 0, (1, -1, 2)), (1, 1, (0, -1, 1)), (-1, 0, (-1, 1, 3)),
      (6, 0, (1, 1, 0)), (-3, 2, (0, 1, 2)), (5, 0, (0, 1, 0))]),
    ([0, -1, 0, 1], [(0, 0, (0, -1, 1)), (1, 1, (-1, -1, 1)), (-3, 1, (-1, 1, 3))])] :
      List (List Int × List (Int64 × Int64 × Int × Int × Nat))).all fun (c, pts) ↦
    match Id.run (chain c (c.length - 1)) with
    | some rows => pts.all fun (nm, dem, r) ↦ Id.run (signsAt rows (rows.size - 1) nm dem) == r
    | none => false

-- The intersection against `_ratpoints_compute_sturm` of the pinned commit, called by a C program
-- that prints with `%a` the intervals it leaves in `domain`, as bits: for each case the intervals
-- that the bisection keeps, which the program leaves for the interval `[-∞, ∞]` of the caller, the
-- intervals of the caller, and the intersection that the program leaves for them; `x ^ 3 - x` at
-- the depth 10 with three intervals of the caller, among them `[-0.0, 0.0]`, which stays;
-- `x - x ^ 3` with a degenerate interval of the caller; `x ^ 2 - 4` on `[-1, 1]`, an empty
-- intersection; `x ^ 3 - 1` on `[2 ^ 62, ∞]` at the depth 5; and `(2 x - 1) (4 x + 3) (x - 5)` at
-- the depth 10 with intervals of the caller that it forgets, holds, lies in, overlaps or only
-- touches.
#guard
  ([([(0xbff0000000000000, 0x0000000000000000), (0x3ff0000000000000, 0x43e0000000000000)],
      [(0xfff0000000000000, 0xbfe0000000000000), (0x8000000000000000, 0x0000000000000000),
        (0x3fe8000000000000, 0x7ff0000000000000)],
      [(0xbff0000000000000, 0xbfe0000000000000), (0x8000000000000000, 0x0000000000000000),
        (0x3ff0000000000000, 0x43e0000000000000)]),
    ([(0xc3e0000000000000, 0xbff0000000000000), (0x0000000000000000, 0x3ff0000000000000)],
      [(0xc008000000000000, 0xc008000000000000), (0x3ff8000000000000, 0x4000000000000000)],
      [(0xc008000000000000, 0xc008000000000000)]),
    ([(0xc3e0000000000000, 0xc000000000000000), (0x4000000000000000, 0x43e0000000000000)],
      [(0xbff0000000000000, 0x3ff0000000000000)], []),
    ([(0x3ff0000000000000, 0x43e0000000000000)], [(0x43d0000000000000, 0x7ff0000000000000)],
      [(0x43d0000000000000, 0x43e0000000000000)]),
    ([(0xbfe8000000000000, 0x3fe0000000000000), (0x4014000000000000, 0x43e0000000000000)],
      [(0xc08f400000000000, 0x408f400000000000)],
      [(0xbfe8000000000000, 0x3fe0000000000000), (0x4014000000000000, 0x408f400000000000)]),
    ([(0xbfe8000000000000, 0x3fe0000000000000), (0x4014000000000000, 0x43e0000000000000)],
      [(0xc024000000000000, 0xc000000000000000), (0xbff0000000000000, 0xbfd0000000000000),
        (0x3fd0000000000000, 0x3fe0000000000000), (0x4010000000000000, 0x4012000000000000)],
      [(0xbfe8000000000000, 0xbfd0000000000000), (0x3fd0000000000000, 0x3fe0000000000000)]),
    ([(0xbfe8000000000000, 0x3fe0000000000000), (0x4014000000000000, 0x43e0000000000000)],
      [(0xbff0000000000000, 0x3ff0000000000000), (0x4010000000000000, 0x7ff0000000000000)],
      [(0xbfe8000000000000, 0x3fe0000000000000), (0x4014000000000000, 0x43e0000000000000)]),
    ([(0xbfe8000000000000, 0x3fe0000000000000), (0x4014000000000000, 0x43e0000000000000)],
      [(0xfff0000000000000, 0xbfe8000000000000), (0x3fe0000000000000, 0x4014000000000000)],
      [(0xbfe8000000000000, 0xbfe8000000000000), (0x3fe0000000000000, 0x3fe0000000000000),
        (0x4014000000000000, 0x4014000000000000)]),
    ([(0xbfe8000000000000, 0x3fe0000000000000), (0x4014000000000000, 0x43e0000000000000)],
      [(0xbfe0000000000000, 0x3fd0000000000000), (0x3fe0000000000000, 0x3fe8000000000000),
        (0x3ff0000000000000, 0x4202a05f20000000)],
      [(0xbfe0000000000000, 0x3fd0000000000000), (0x3fe0000000000000, 0x3fe0000000000000),
        (0x4014000000000000, 0x4202a05f20000000)])] :
      List (List (UInt64 × UInt64) × List (UInt64 × UInt64) × List (UInt64 × UInt64))).all
    fun (loc, ivs, out) ↦
  let doubles (l : List (UInt64 × UInt64)) : Array (Double × Double) :=
    (l.map fun (a, b) ↦ (⟨a⟩, ⟨b⟩)).toArray
  (Id.run (intersect (doubles loc) (doubles ivs))).toList.map (fun (l, u) ↦ (l.bits, u.bits)) == out

-- The Sturm step against a C program that calls `_ratpoints_compute_sturm` of the pinned commit and
-- prints the intervals it leaves in `domain` with `%a`, as bits: for each case the depth, the
-- intervals of the caller, the coefficients `c₀, …, c_d` and the intervals (none for the return of
-- `-1`); `x ^ 3 - 2` and `x ^ 4 - 5 x ^ 2 + 1` with a few real intervals, the ends at infinity
-- `±2 ^ 63`; `-x ^ 4 - 1`, negative everywhere (the exit, no interval); `(x + 1) ^ 2`, not
-- squarefree; `(2 x - 1) (4 x + 3) (x - 5)`, whose roots the midpoints hit, at the depths 10, 0, 1,
-- 2 and 55; `x ^ 2 - 2` at the depths 55 and 30; `x ^ 3 - x` with three intervals of the caller,
-- among them `[-0.0, 0.0]`, which stays; `x ^ 2 - 4` on `[-1, 1]`, an empty intersection;
-- `4 - x ^ 2`; `3 + 2 x`, of degree 1; `x ^ 2 + x + 1`, positive everywhere; two close roots;
-- coefficients of 70 bits; `x ^ 3 - 1` on `[2 ^ 62, ∞]`; and a degenerate interval of the caller.
#guard
  ([
    (10, [(0xc024000000000000, 0x4024000000000000)],
      [-2, 0, 0, 1], some [(0x3ff4200000000000, 0x4024000000000000)]),
    (10, [(0xfff0000000000000, 0x7ff0000000000000)],
      [1, 0, -5, 0, 1], some [(0xc3e0000000000000, 0xc001800000000000),
        (0xbfdd400000000000, 0x3fdd400000000000), (0x4001800000000000, 0x43e0000000000000)]),
    (10, [(0xc024000000000000, 0x4024000000000000)], [-1, 0, 0, 0, -1], some []),
    (10, [(0xc024000000000000, 0x4024000000000000)], [1, 2, 1], none),
    (10, [(0xc08f400000000000, 0x408f400000000000)],
      [15, -13, -38, 8], some [(0xbfe8000000000000, 0x3fe0000000000000),
        (0x4014000000000000, 0x408f400000000000)]),
    (0, [(0xc08f400000000000, 0x408f400000000000)],
      [15, -13, -38, 8], some [(0xc08f400000000000, 0x408f400000000000)]),
    (1, [(0xc08f400000000000, 0x408f400000000000)],
      [15, -13, -38, 8], some [(0xc08f400000000000, 0x408f400000000000)]),
    (2, [(0xc08f400000000000, 0x408f400000000000)],
      [15, -13, -38, 8], some [(0xbff0000000000000, 0x408f400000000000)]),
    (55, [(0xc08f400000000000, 0x408f400000000000)],
      [15, -13, -38, 8], some [(0xbfe8000000000000, 0x3fe0000000000000),
        (0x4014000000000000, 0x408f400000000000)]),
    (55, [(0xc3e0000000000000, 0x43e0000000000000)],
      [-2, 0, 1], some [(0xc3e0000000000000, 0xbff6a09e667f3bcc),
        (0x3ff6a09e667f3bcc, 0x43e0000000000000)]),
    (30, [(0xc024000000000000, 0x4024000000000000)],
      [-2, 0, 1], some [(0xc024000000000000, 0xbff6a09e66000000),
        (0x3ff6a09e66000000, 0x4024000000000000)]),
    (10, [(0xfff0000000000000, 0xbfe0000000000000), (0x8000000000000000, 0x0000000000000000),
        (0x3fe8000000000000, 0x7ff0000000000000)],
      [0, -1, 0, 1], some [(0xbff0000000000000, 0xbfe0000000000000),
        (0x8000000000000000, 0x0000000000000000), (0x3ff0000000000000, 0x43e0000000000000)]),
    (10, [(0xbff0000000000000, 0x3ff0000000000000)], [-4, 0, 1], some []),
    (10, [(0xc08f400000000000, 0x408f400000000000)],
      [4, 0, -1], some [(0xc000000000000000, 0x4000000000000000)]),
    (10, [(0xc024000000000000, 0x4024000000000000)],
      [3, 2], some [(0xbff8000000000000, 0x4024000000000000)]),
    (10, [(0xc1cdcd6500000000, 0x41cdcd6500000000)],
      [1, 1, 1], some [(0xc1cdcd6500000000, 0x41cdcd6500000000)]),
    (20, [(0xc12e848000000000, 0x412e848000000000)],
      [2002000, -3001000, -1000, 1000000], some [(0xc000000000000000, 0x3ff0000000000000),
        (0x3ff0041800000000, 0x412e848000000000)]),
    (10, [(0xc024000000000000, 0x4024000000000000)],
      [123456789012345678901, -98765432109876543210, 5, 7, -1000000000000000000],
      some [(0xc014000000000000, 0x3ff3c00000000000)]),
    (5, [(0x43d0000000000000, 0x7ff0000000000000)],
      [-1, 0, 0, 1], some [(0x43d0000000000000, 0x43e0000000000000)]),
    (10, [(0xc008000000000000, 0xc008000000000000), (0x3ff8000000000000, 0x4000000000000000)],
      [0, 1, 0, -1], some [(0xc008000000000000, 0xc008000000000000)])] :
      List (Nat × List (UInt64 × UInt64) × List Int × Option (List (UInt64 × UInt64)))).all
    fun (iter, ivs, c, exp) ↦
  (Id.run (computeSturm c (c.length - 1) iter (ivs.toArray.map fun (l, u) ↦ (⟨l⟩, ⟨u⟩)))).map
    (·.toList.map fun (l, u) ↦ (l.bits, u.bits)) == exp

-- The bisection keeps at most `1 + ⌊d / 2⌋` intervals, the size of the array `ivlocal` of the C
-- code, at the depths from 0 to 55, here for three products of linear factors with rational roots
-- (of degrees 3, 3 and 4), `x ^ 4 - 5 x ^ 2 + 1` with four irrational real roots, which reaches the
-- bound, an irreducible quintic with one real root, and `x ^ 12 + (x - 1) (x - 2) (x - 3)`, which
-- has two.
#guard
  let polys : List (List Int) := [[15, -13, -38, 8], [1, 0, -5, 0, 1], [0, -1, 0, 1],
    [-24, 50, -35, 10, -1], [2, -3, -3, 2, 3, -2], [-6, 11, -6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]]
  polys.all fun c ↦ (List.range 56).all fun iter ↦
    match Id.run (chain c (c.length - 1)) with
    | none => false
    | some rows =>
      let (c1, c2) := Id.run (countsAtInfinity rows (rows.size - 1))
      let s := (c.getD (c.length - 1) 0).sign
      (Id.run (iterate rows (rows.size - 1) iter (-longMax) longMax 0 0 c2 c1
        (if (c.length - 1) % 2 = 1 then -s else s) s 0 #[])).size ≤ 1 + (c.length - 1) / 2

end Sturm

end Ratpoints

end
