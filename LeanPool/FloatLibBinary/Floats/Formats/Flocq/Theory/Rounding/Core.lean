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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Core

/-!
# Rounding modes and a half-ULP error bound

Rounding on `ℝ` reduces to integer rounding of a scaled mantissa, with the following operators
and validity contracts:

- rounding modes `rnd : ℝ → ℤ` (floor/ceil/trunc/nearest-even),
- the validity typeclasses `ValidRnd` and `ValidRndToNearest`,
- the core rounding operator `round`,
- the standard bound `abs(round … x - x) ≤ ulp(x)/2` for round-to-nearest.

These definitions are used by `NF` (the rounded scalar type) and by
`BinaryInterchange.Model.roundAt`, which connects generic proofs to the finite semantics of an
explicit binary descriptor.

## References

- IEEE Std 754-2019, "IEEE Standard for Floating-Point Arithmetic".
- D. Goldberg, "What Every Computer Scientist Should Know About Floating-Point Arithmetic",
  ACM Computing Surveys, 1991.
- N. J. Higham, "Accuracy and Stability of Numerical Algorithms", SIAM, 2nd ed., 2002.
- The Flocq Coq library, whose radix-parametric rounding model guides this formalization.
-/

@[expose] public section


namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-- Round toward negative infinity (floor) -/
noncomputable def floorRound : ℝ → ℤ := fun x => ⌊x⌋

/-- Round toward positive infinity (ceiling) -/
noncomputable def ceilRound : ℝ → ℤ := fun x => ⌈x⌉

/-- Round toward zero (truncation) -/
noncomputable def truncRound : ℝ → ℤ := fun x =>
  if x < 0 then ⌈x⌉ else ⌊x⌋

/-- Toward-zero integer rounding agrees with floor on nonnegative inputs. -/
theorem truncRound_eq_floor {x : ℝ} (hx : 0 ≤ x) :
    truncRound x = floorRound x := by
  simp [truncRound, floorRound, not_lt.mpr hx]

/-- Toward-zero integer rounding agrees with ceiling on nonpositive inputs. -/
theorem truncRound_eq_ceil {x : ℝ} (hx : x ≤ 0) :
    truncRound x = ceilRound x := by
  by_cases hzero : x = 0
  · subst x
    simp [truncRound, ceilRound]
  · simp [truncRound, ceilRound, lt_of_le_of_ne hx hzero]

/-- Round to nearest, ties to even -/
noncomputable def nearestEven : ℝ → ℤ := fun x =>
  let f := ⌊x⌋
  if x - f < 1 / 2 then f
  else if x - f > 1 / 2 then f + 1
  else if Even f then f else f + 1

/--
A monotone integer-rounding function that fixes every integer.
-/
class ValidRnd (rnd : ℝ → ℤ) : Prop where
  /-- The rounding rule preserves the order of its real inputs. -/
  monotone : ∀ x y, x ≤ y → rnd x ≤ rnd y
  /-- Every integer is fixed by the rounding rule. -/
  id : ∀ n : ℤ, rnd n = n

/--
Rounding modes with a half-unit error bound on the rounded integer.

This matches "round-to-nearest" style roundings (ties can be resolved arbitrarily):
`|rnd x - x| ≤ 1 / 2` for all `x`.
-/
class ValidRndToNearest (rnd : ℝ → ℤ) : Prop extends ValidRnd rnd where
  /-- Rounding changes a real input by at most one half on the integer grid. -/
  abs_sub_le_half : ∀ x : ℝ, abs ((rnd x : ℝ) - x) ≤ (2⁻¹ : ℝ)

/--
Round `x` to the integer grid with spacing `step`.

This fixed-scale operation is the common core of fixed-point arithmetic and affine quantization.
Unlike `round`, the scale is supplied explicitly rather than chosen from the magnitude of
`x` by an exponent format. Requiring positivity prevents a zero scale from silently turning the
operation into the constant-zero map through totalized real division.
-/
noncomputable def roundAtScale (rnd : ℝ → ℤ) (step : ℝ) (_hstep : 0 < step) (x : ℝ) : ℝ :=
  (rnd (x / step) : ℝ) * step

/-- `floorRound` is a valid rounding mode: it is monotone and fixes integers. -/
instance : ValidRnd floorRound where
  monotone := fun _ _ h => Int.floor_mono h
  id := fun n => Int.floor_intCast n

/-- `ceilRound` is a valid rounding mode: it is monotone and fixes integers. -/
instance : ValidRnd ceilRound where
  monotone := fun _ _ h => Int.ceil_mono h
  id := fun n => Int.ceil_intCast n

/-- Toward-zero integer rounding is monotone and fixes integers. -/
instance : ValidRnd truncRound where
  monotone := by
    intro x y hxy
    by_cases hx : x < 0
    · by_cases hy : y < 0
      · rw [truncRound_eq_ceil hx.le, truncRound_eq_ceil hy.le]
        exact Int.ceil_mono hxy
      · rw [truncRound_eq_ceil hx.le,
            truncRound_eq_floor (le_of_not_gt hy)]
        have hleft : ceilRound x ≤ 0 := by
          unfold ceilRound
          exact Int.ceil_le.mpr (by simpa using hx.le)
        have hright : 0 ≤ floorRound y := by
          unfold floorRound
          exact Int.le_floor.mpr (by simpa using le_of_not_gt hy)
        exact hleft.trans hright
    · have hx0 : 0 ≤ x := le_of_not_gt hx
      have hy0 : 0 ≤ y := hx0.trans hxy
      rw [truncRound_eq_floor hx0, truncRound_eq_floor hy0]
      exact Int.floor_mono hxy
  id := by
    intro n
    by_cases hn : n < 0
    · simp [truncRound, hn]
    · simp [truncRound, hn]

/--
Basic bounds for nearest-even rounding.

The rounded integer is either `⌊x⌋` or its successor. This localizes the monotonicity proof to the
case where two inputs have the same floor.
-/
lemma nearestEven_bounds (x : ℝ) :
    ⌊x⌋ ≤ nearestEven x ∧ nearestEven x ≤ ⌊x⌋ + 1 := by
  simp only [nearestEven]
  split_ifs <;> simp

/--
Nearest-even rounding depends only on the floor and on how the fractional part compares with
`1 / 2`. Two inputs with the same floor whose fractional parts fall on the same side of `1 / 2`
round
to the same integer.
-/
theorem nearestEven_congr {x y : ℝ} (hfloor : ⌊x⌋ = ⌊y⌋)
    (hlt : x - ⌊x⌋ < 1 / 2 ↔ y - ⌊y⌋ < 1 / 2)
    (hgt : x - ⌊x⌋ > 1 / 2 ↔ y - ⌊y⌋ > 1 / 2) :
    nearestEven x = nearestEven y := by
  simp only [nearestEven]
  rw [hfloor] at hlt hgt ⊢
  grind

/--
Nearest-even rounds down when the fractional part is strictly less than `1 / 2`.
-/
lemma nearestEven_eq_floor_of_frac_lt_half (x : ℝ) (h : x - ⌊x⌋ < 1 / 2) :
    nearestEven x = ⌊x⌋ := by
  simp only [nearestEven, h, ite_true]

/--
Nearest-even rounds up when the fractional part is strictly greater than `1 / 2`.
-/
lemma nearestEven_eq_ceil_of_frac_gt_half (x : ℝ) (h : x - ⌊x⌋ > 1 / 2) :
    nearestEven x = ⌊x⌋ + 1 := by
  simp only [nearestEven]
  have h1 : ¬(x - ⌊x⌋ < 1 / 2) := not_lt.mpr (le_of_lt h)
  simp only [h1, ite_false, h, ite_true]

/--
Nearest-even tie-breaking: when the fractional part is exactly `1 / 2` and the floor is even,
round down to the even integer.
-/
lemma nearestEven_eq_floor_of_frac_half_even (x : ℝ) (h1 : x - ⌊x⌋ = 1 / 2) (h2 : Even ⌊x⌋) :
    nearestEven x = ⌊x⌋ := by
  simp only [nearestEven]
  have h3 : ¬(x - ⌊x⌋ < 1 / 2) := by rw [h1]; norm_num
  have h4 : ¬(x - ⌊x⌋ > 1 / 2) := by rw [h1]; norm_num
  simp only [h3, h4, ite_false, h2, ite_true]

/--
Nearest-even tie-breaking: when the fractional part is exactly `1 / 2` and the floor is odd,
round up to the even integer.
-/
lemma nearestEven_eq_ceil_of_frac_half_odd (x : ℝ) (h1 : x - ⌊x⌋ = 1 / 2) (h2 : ¬Even ⌊x⌋) :
    nearestEven x = ⌊x⌋ + 1 := by
  simp only [nearestEven]
  have h3 : ¬(x - ⌊x⌋ < 1 / 2) := by rw [h1]; norm_num
  have h4 : ¬(x - ⌊x⌋ > 1 / 2) := by rw [h1]; norm_num
  simp only [h3, h4, ite_false, h2, ite_false]

/-- `nearestEven` is a valid rounding mode: it is monotone and fixes integers. -/
instance : ValidRnd nearestEven where
  monotone := by
    intro x y hxy
    by_cases hfloor : ⌊x⌋ = ⌊y⌋
    · have hfrac : x - ⌊x⌋ ≤ y - ⌊y⌋ := by
        rw [hfloor]
        linarith
      by_cases hxlt : x - ⌊x⌋ < 1 / 2
      · rw [nearestEven_eq_floor_of_frac_lt_half x hxlt, hfloor]
        exact (nearestEven_bounds y).1
      · have hxge : (1 / 2 : ℝ) ≤ x - ⌊x⌋ := le_of_not_gt hxlt
        by_cases hxgt : x - ⌊x⌋ > 1 / 2
        · have hygt : y - ⌊y⌋ > (1 / 2 : ℝ) :=
            lt_of_lt_of_le hxgt hfrac
          rw [nearestEven_eq_ceil_of_frac_gt_half x hxgt,
            nearestEven_eq_ceil_of_frac_gt_half y hygt, hfloor]
        · have hxeq : x - ⌊x⌋ = (1 / 2 : ℝ) :=
            le_antisymm (le_of_not_gt hxgt) hxge
          by_cases heven : Even ⌊x⌋
          · rw [nearestEven_eq_floor_of_frac_half_even x hxeq heven, hfloor]
            exact (nearestEven_bounds y).1
          · by_cases hygt : y - ⌊y⌋ > 1 / 2
            · rw [nearestEven_eq_ceil_of_frac_half_odd x hxeq heven,
                nearestEven_eq_ceil_of_frac_gt_half y hygt, hfloor]
            · have hyge : (1 / 2 : ℝ) ≤ y - ⌊y⌋ := by
                linarith
              have hyeq : y - ⌊y⌋ = (1 / 2 : ℝ) :=
                le_antisymm (le_of_not_gt hygt) hyge
              have hyodd : ¬Even ⌊y⌋ := by
                rwa [← hfloor]
              rw [nearestEven_eq_ceil_of_frac_half_odd x hxeq heven,
                nearestEven_eq_ceil_of_frac_half_odd y hyeq hyodd, hfloor]
    · have hfloorlt : ⌊x⌋ < ⌊y⌋ :=
        Int.lt_iff_le_and_ne.mpr ⟨Int.floor_mono hxy, hfloor⟩
      calc
        nearestEven x ≤ ⌊x⌋ + 1 := (nearestEven_bounds x).2
        _ ≤ ⌊y⌋ := Int.add_one_le_iff.mpr hfloorlt
        _ ≤ nearestEven y := (nearestEven_bounds y).1
  id := by
    intro n
    simp [nearestEven]

/-- Nearest-even has the same distance from the input as Mathlib's ties-up nearest integer. -/
theorem nearestEven_abs_eq_round (x : ℝ) :
    abs ((nearestEven x : ℝ) - x) = abs ((round x : ℝ) - x) := by
  by_cases hlt : x - (⌊x⌋ : ℝ) < 1 / 2
  · have hcond : 2 * Int.fract x < 1 := by
      simp only [Int.fract]
      linarith
    rw [nearestEven_eq_floor_of_frac_lt_half x hlt]
    simp [round, hcond]
  · by_cases hgt : x - (⌊x⌋ : ℝ) > 1 / 2
    · have hcond : ¬2 * Int.fract x < 1 := by
        simp only [Int.fract]
        linarith
      have hxnotint : x ∉ Set.range ((↑·) : ℤ → ℝ) := by
        rintro ⟨n, rfl⟩
        norm_num at hgt
      have hceil : ⌈x⌉ = ⌊x⌋ + 1 := (Int.ceil_eq_floor_add_one_iff_notMem x).2 hxnotint
      rw [nearestEven_eq_ceil_of_frac_gt_half x hgt]
      have hround : round x = ⌈x⌉ := by simp [round, hcond]
      rw [hround, hceil]
    · have heq : x - (⌊x⌋ : ℝ) = 1 / 2 := by
        linarith
      have hcond : ¬2 * Int.fract x < 1 := by
        simp only [Int.fract]
        linarith
      have hxnotint : x ∉ Set.range ((↑·) : ℤ → ℝ) := by
        rintro ⟨n, rfl⟩
        norm_num at heq
      have hceil : ⌈x⌉ = ⌊x⌋ + 1 := (Int.ceil_eq_floor_add_one_iff_notMem x).2 hxnotint
      by_cases heven : Even ⌊x⌋
      · rw [nearestEven_eq_floor_of_frac_half_even x heq heven]
        have hround : round x = ⌈x⌉ := by simp [round, hcond]
        rw [hround, hceil]
        have hleft : (⌊x⌋ : ℝ) - x = -(1 / 2 : ℝ) := by linarith
        have hright : ((⌊x⌋ + 1 : ℤ) : ℝ) - x = 1 / 2 := by
          push_cast
          linarith
        rw [hleft, hright]
        norm_num
      · rw [nearestEven_eq_ceil_of_frac_half_odd x heq heven]
        have hround : round x = ⌈x⌉ := by simp [round, hcond]
        rw [hround, hceil]

/-- Nearest-even integer rounding changes a real number by at most one half. -/
lemma nearestEven_abs_sub_le_half (x : ℝ) :
    abs ((nearestEven x : ℝ) - x) ≤ (2⁻¹ : ℝ) := by
  rw [nearestEven_abs_eq_round, abs_sub_comm]
  simpa using abs_sub_round x

/-- Nearest-even minimizes distance to the input among all integers. -/
theorem nearestEven_is_nearest_integer (x : ℝ) (n : ℤ) :
    abs ((nearestEven x : ℝ) - x) ≤ abs ((n : ℝ) - x) := by
  rw [nearestEven_abs_eq_round x, abs_sub_comm, abs_sub_comm (n : ℝ) x]
  exact round_le x n

/-- `nearestEven` satisfies the half-unit error bound `|rnd x - x| ≤ 1 / 2`. -/
instance : ValidRndToNearest nearestEven where
  monotone := ValidRnd.monotone (rnd := nearestEven)
  id := ValidRnd.id (rnd := nearestEven)
  abs_sub_le_half := nearestEven_abs_sub_le_half

/--
Round the scaled mantissa to an integer, then reconstruct the value at the canonical exponent
of the input.
-/
noncomputable def round (rnd : ℝ → ℤ) (x : ℝ) : ℝ :=
  toReal (β := β) { mantissa := rnd (scaledMantissa β fexp x),
                            exponent := cexp β fexp x }

omit [ValidExp fexp] in
/-- The scaled mantissa is the input divided by its canonical radix power. -/
theorem scaledMantissa_eq_div (x : ℝ) :
    scaledMantissa β fexp x = x / bpow β (cexp β fexp x) := by
  simp [scaledMantissa, bpow.neg_exp, div_eq_mul_inv]

omit [ValidExp fexp] in
/--
An exactly representable value has an integral mantissa at its canonical exponent.
-/
theorem scaled_mantissa_int_of_generic (x : ℝ) (hx : genericFormat β fexp x) :
    ∃ n : ℤ, scaledMantissa β fexp x = n := by
  let m := ⌊scaledMantissa β fexp x⌋
  let e := cexp β fexp x
  use m
  have h_repr : x = m * bpow β e := by
    simp only [genericFormat, toReal] at hx
    exact hx
  calc scaledMantissa β fexp x
    = x * bpow β (-cexp β fexp x)             := by rfl
    _ = x * bpow β (-e)                              := by rfl
    _ = (m * bpow β e) * bpow β (-e)          := by rw [h_repr]
    _ = m * (bpow β e * bpow β (-e))          := by rw [mul_assoc]
    _ = m * bpow β (e + (-e))                        := by rw [← bpow.add_exp]
    _ = m * bpow β 0                                 := by simp [add_neg_cancel]
    _ = m * 1                                               := by simp [bpow,
      Numerics.Radix.toReal]
    _ = m                                                   := by rw [mul_one]
    _ = ↑m                                                  := by simp

omit [ValidExp fexp] in
/--
Rounding preserves exactly-representable numbers.

This is the Flocq-style `round_generic` law: every valid integer rounder fixes the integral
canonical mantissa, so reconstructing the value returns the original grid point.
-/
@[simp] theorem round_preserves_generic (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ)
    (hx : genericFormat β fexp x) :
    round (β := β) (fexp := fexp) rnd x = x := by
  simp only [round]
  obtain ⟨n, hn⟩ := scaled_mantissa_int_of_generic x hx
  have h_rnd : rnd (scaledMantissa β fexp x) = n := by
    rw [hn]
    exact ValidRnd.id n
  have h_floor : n = ⌊scaledMantissa β fexp x⌋ := by
    rw [hn]
    simp only [Int.floor_intCast]
  rw [h_rnd, h_floor]
  simp only [genericFormat] at hx
  exact hx.symm

omit [ValidExp fexp] in
/--
Multiplying the canonical scaled mantissa by its radix power reconstructs the original value.
-/
lemma scaled_mantissa_mul_bpow (x : ℝ) :
    scaledMantissa β fexp x * bpow β (cexp β fexp x) = x := by
  simp only [scaledMantissa]
  rw [mul_assoc, ← bpow.add_exp]
  simp only [bpow]
  simp [Numerics.Radix.toReal, mul_one]

omit [ValidExp fexp] in
/-- An integral canonical scaled mantissa is sufficient for exact representability. -/
theorem generic_format_of_scaled_mantissa_int (x : ℝ) (n : ℤ)
    (h : scaledMantissa β fexp x = n) : genericFormat β fexp x := by
  unfold genericFormat toReal
  calc
    x = scaledMantissa β fexp x * bpow β (cexp β fexp x) :=
      (scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x).symm
    _ = (n : ℝ) * bpow β (cexp β fexp x) := by rw [h]
    _ = (⌊scaledMantissa β fexp x⌋ : ℝ) *
          bpow β (cexp β fexp x) := by rw [h]; simp

omit [ValidExp fexp] in
/-- Exact representability is equivalent to integrality of the canonical scaled mantissa. -/
theorem generic_format_iff_scaled_mantissa_int (x : ℝ) :
    genericFormat β fexp x ↔ ∃ n : ℤ, scaledMantissa β fexp x = n := by
  constructor
  · exact scaled_mantissa_int_of_generic (β := β) (fexp := fexp) x
  · rintro ⟨n, hn⟩
    exact generic_format_of_scaled_mantissa_int (β := β) (fexp := fexp) x n hn

omit [ValidExp fexp] in
/--
Half-ULP error bound for `round` under round-to-nearest.

This is the basic “one-step” bound used by most error propagation arguments:
`round` deviates from `x` by at most half an ulp at the chosen exponent scale.
-/
theorem error_bound_ulp (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) :
    abs (round (β := β) (fexp := fexp) rnd x - x) ≤ ulp β fexp x / 2 := by
  by_cases hx : x = 0
  · subst hx
    have hr0 : rnd 0 = 0 := by simpa using (ValidRnd.id (rnd := rnd) (0 : ℤ))
    have hround : round (β := β) (fexp := fexp) rnd 0 = 0 := by
      simp [round, scaledMantissa, cexp, magnitude, toReal, hr0]
    rw [hround, sub_self, abs_zero]
    exact div_nonneg (ulp.nonneg (β := β) (fexp := fexp) 0) (by norm_num)
  · simp only [ulp, hx, ↓reduceIte]
    simp only [round, toReal]
    set s : ℝ := scaledMantissa β fexp x
    set e : ℤ := cexp β fexp x
    have hxrepr : s * bpow β e = x := by
      subst s e
      simpa using (scaled_mantissa_mul_bpow (β := β) (fexp := fexp) x)
    rw [← hxrepr]
    rw [← sub_mul]
    rw [abs_mul]
    have hbpos : 0 < bpow β e := bpow.pos β e
    simp [abs_of_pos hbpos]
    have h := ValidRndToNearest.abs_sub_le_half (rnd := rnd) s
    have hbnonneg : 0 ≤ bpow β e := le_of_lt hbpos
    have hmul := mul_le_mul_of_nonneg_right h hbnonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, mul_right_comm] using hmul

/-! ## Named standard modes -/

/-- The four standard rounding-direction attributes used by the generic float model. -/
inductive RoundingMode where
  /--
  Round to the nearest value, resolving a tie toward an even integer at the selected scale.
  Under the usual Flocq conditions (in particular, excluding the precision-one even-radix corner
  case), this agrees with the familiar even canonical-significand description.
  -/
  | nearestEven
  /-- Round toward zero. -/
  | towardZero
  /-- Round toward positive infinity. -/
  | towardPositive
  /-- Round toward negative infinity. -/
  | towardNegative
  deriving DecidableEq, Repr

namespace RoundingMode

/-- Interpret a named mode as the integer-rounding function used by `round`. -/
noncomputable def roundingFunction : RoundingMode → ℝ → ℤ
  | .nearestEven => FloatLib.Floats.Formats.Flocq.nearestEven
  | .towardZero => truncRound
  | .towardPositive => ceilRound
  | .towardNegative => floorRound

/-- Every named standard mode satisfies the generic rounding-function laws. -/
instance (mode : RoundingMode) : ValidRnd mode.roundingFunction := by
  cases mode with
  | nearestEven =>
      change ValidRnd FloatLib.Floats.Formats.Flocq.nearestEven
      infer_instance
  | towardZero => change ValidRnd truncRound; infer_instance
  | towardPositive => change ValidRnd ceilRound; infer_instance
  | towardNegative => change ValidRnd floorRound; infer_instance

/-- Round a real value into a generic format using a named standard mode. -/
noncomputable def round (mode : RoundingMode) {β : Numerics.Radix} {fexp : ℤ → ℤ}
    (x : ℝ) : ℝ :=
  FloatLib.Floats.Formats.Flocq.round
    (β := β) (fexp := fexp) mode.roundingFunction x

/-- Package `round` as a mantissa/exponent value in the selected format. -/
noncomputable def roundedFloat (mode : RoundingMode) {β : Numerics.Radix} {fexp : ℤ → ℤ}
    (x : ℝ) : FloatRep β :=
  { mantissa := mode.roundingFunction (scaledMantissa β fexp x)
    exponent := cexp β fexp x }

/-- `roundedFloat` represents exactly the value returned by `round`. -/
@[simp] theorem toReal_roundedFloat (mode : RoundingMode) {β : Numerics.Radix}
    {fexp : ℤ → ℤ} (x : ℝ) :
    toReal (mode.roundedFloat (β := β) (fexp := fexp) x) =
      mode.round (β := β) (fexp := fexp) x := by
  rfl

/-- Every named standard mode fixes values already in the generic format. -/
theorem round_eq_of_generic (mode : RoundingMode) {β : Numerics.Radix}
    {fexp : ℤ → ℤ} {x : ℝ}
    (hx : genericFormat (β := β) (fexp := fexp) x) :
    mode.round (β := β) (fexp := fexp) x = x := by
  exact round_preserves_generic mode.roundingFunction x hx

end RoundingMode

end FloatLib.Floats.Formats.Flocq
