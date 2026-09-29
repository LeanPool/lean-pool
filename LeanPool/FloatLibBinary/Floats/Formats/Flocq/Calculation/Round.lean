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

public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Calculation.Bracket
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Calculation.Operations
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Format.Digits
public import LeanPool.FloatLibBinary.Floats.Formats.Flocq.Theory.Rounding.Nearest

/-!
# Rounding from a Certified Bracket

The effective calculation layer identifies a unit interval `[m, m + 1)` and a location inside it.
This file turns that finite location data into the integer selected by directed or nearest rounding
and proves agreement with the rounded-real definitions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- Unit-interval specialization of `Inbetween`. -/
abbrev InbetweenInt (m : ℤ) (x : ℝ) (location : Location) : Prop :=
  Inbetween (m : ℝ) ((m + 1 : ℤ) : ℝ) x location

/-- Canonical location obtained from the floor bracket of a real value. -/
noncomputable def integerLocation (x : ℝ) : Location :=
  inbetweenLocation (⌊x⌋ : ℝ) ((⌊x⌋ + 1 : ℤ) : ℝ) x

/-- Every real value satisfies its canonical floor bracket. -/
theorem integerLocation_spec (x : ℝ) :
    InbetweenInt ⌊x⌋ x (integerLocation x) := by
  apply inbetweenLocation_spec
  · norm_num
  · refine ⟨Int.floor_le x, ?_⟩
    norm_num only [Int.cast_add, Int.cast_one]
    exact Int.lt_floor_add_one x

/-- Increment an integer when the supplied decision is true. -/
def conditionalIncrement (increment : Bool) (m : ℤ) : ℤ :=
  if increment then m + 1 else m

/-- A conditional increment always selects one of the two bracket endpoints. -/
theorem conditionalIncrement_bounds (increment : Bool) (m : ℤ) :
    m ≤ conditionalIncrement increment m ∧
      conditionalIncrement increment m ≤ m + 1 := by
  cases increment <;> simp [conditionalIncrement]

/-- Upward rounding increments exactly when the location is inexact. -/
def roundUpLocation : Location → Bool
  | .exact => false
  | .inexact _ => true

/-- Nearest rounding increments above the midpoint and delegates exact ties to `chooseUp`. -/
def roundNearestLocation (chooseUp : ℤ → Bool) (m : ℤ) : Location → Bool
  | .exact => false
  | .inexact .lt => false
  | .inexact .eq => chooseUp m
  | .inexact .gt => true

/-- Tie decision used by nearest-even rounding: increment exactly when the lower integer is odd. -/
def nearestEvenChoice (m : ℤ) : Bool := decide (¬Even m)

/-- Choice-based nearest rounding with the parity decision is FloatLib's nearest-even mode. -/
theorem nearestChoice_even_eq (x : ℝ) :
    nearestChoice nearestEvenChoice x = nearestEven x := by
  simp only [nearestChoice, nearestEven, nearestEvenChoice]
  rw [Int.fract]
  split
  · rfl
  · split
    · rfl
    · by_cases heven : Even ⌊x⌋
      · simp [heven]
      · simp [heven]

/-- A certified unit bracket determines floor exactly. -/
theorem inbetweenInt_floor {m : ℤ} {x : ℝ} {location : Location}
    (hl : InbetweenInt m x location) : floorRound x = m := by
  unfold floorRound
  cases hl with
  | exact hx => simp [hx]
  | inexact _ hx _ =>
      exact Int.floor_eq_iff.mpr ⟨by exact_mod_cast hx.1.le, by simpa using hx.2⟩

/-- A certified unit bracket determines ceiling from exactness alone. -/
theorem inbetweenInt_ceil {m : ℤ} {x : ℝ} {location : Location}
    (hl : InbetweenInt m x location) :
    ceilRound x = conditionalIncrement (roundUpLocation location) m := by
  unfold ceilRound
  cases hl with
  | exact hx => simp [hx, conditionalIncrement, roundUpLocation]
  | inexact order hx _ =>
      have hceil : ⌈x⌉ = m + 1 :=
        Int.ceil_eq_iff.mpr ⟨by simpa using hx.1, by simpa using hx.2.le⟩
      simpa [conditionalIncrement, roundUpLocation] using hceil

/-- A certified unit bracket computes arbitrary-tie nearest rounding. -/
theorem inbetweenInt_nearestChoice (chooseUp : ℤ → Bool)
    {m : ℤ} {x : ℝ} {location : Location}
    (hl : InbetweenInt m x location) :
    nearestChoice chooseUp x =
      conditionalIncrement (roundNearestLocation chooseUp m location) m := by
  have hfloor := inbetweenInt_floor hl
  cases hl with
  | exact hx =>
      subst x
      simp [nearestChoice, conditionalIncrement, roundNearestLocation]
  | inexact order hx hmid =>
      change ⌊x⌋ = m at hfloor
      have hfract : Int.fract x = x - m := by
        rw [Int.fract]
        rw [hfloor]
      cases order with
      | lt =>
          have hlt : Int.fract x < (2⁻¹ : ℝ) := by
            rw [cmp_eq_lt_iff] at hmid
            rw [hfract]
            norm_num only [Int.cast_add, Int.cast_one] at hmid
            norm_num at hmid ⊢
            linarith
          simp [nearestChoice, hfloor, hlt, conditionalIncrement,
            roundNearestLocation]
      | eq =>
          have heq : Int.fract x = (2⁻¹ : ℝ) := by
            rw [cmp_eq_eq_iff] at hmid
            rw [hfract]
            norm_num only [Int.cast_add, Int.cast_one] at hmid
            norm_num at hmid ⊢
            linarith
          simp [nearestChoice, hfloor, heq, conditionalIncrement,
            roundNearestLocation]
          rfl
      | gt =>
          have hgt : Int.fract x > (2⁻¹ : ℝ) := by
            rw [cmp_eq_gt_iff] at hmid
            rw [hfract]
            norm_num only [Int.cast_add, Int.cast_one] at hmid
            norm_num at hmid ⊢
            linarith
          have hnlt : ¬Int.fract x < (2⁻¹ : ℝ) := not_lt.mpr hgt.le
          simp [nearestChoice, hfloor, hnlt, hgt, conditionalIncrement,
            roundNearestLocation]

/-- A certified unit bracket computes nearest-even rounding. -/
theorem inbetweenInt_nearestEven {m : ℤ} {x : ℝ} {location : Location}
    (hl : InbetweenInt m x location) :
    nearestEven x =
      conditionalIncrement
        (roundNearestLocation nearestEvenChoice m location) m := by
  rw [← nearestChoice_even_eq]
  exact inbetweenInt_nearestChoice nearestEvenChoice hl

/-! ## Mantissa truncation -/

/-- Mantissa, exponent, and location carried by an effective rounding calculation. -/
structure TruncationState where
  /-- Lower-endpoint mantissa. -/
  mantissa : ℤ
  /-- Shared radix exponent. -/
  exponent : ℤ
  /-- Input location within the represented unit interval. -/
  location : Location
  deriving DecidableEq, Repr

/-- Real interval and location denoted by a truncation state. -/
abbrev TruncationState.Brackets (β : Numerics.Radix)
    (state : TruncationState) (x : ℝ) : Prop :=
  Inbetween
    (toReal (β := β) { mantissa := state.mantissa, exponent := state.exponent })
    (toReal (β := β) { mantissa := state.mantissa + 1, exponent := state.exponent })
    x state.location

/-- A positive value bracketed by a truncation state forces a nonnegative lower mantissa. -/
theorem TruncationState.mantissa_nonneg_of_brackets
    (β : Numerics.Radix) (state : TruncationState) {x : ℝ}
    (hx : 0 < x) (hl : state.Brackets β x) : 0 ≤ state.mantissa := by
  have hstep : 0 < bpow β state.exponent := bpow.pos β state.exponent
  have hordered :
      toReal (β := β) { mantissa := state.mantissa, exponent := state.exponent } <
        toReal (β := β) { mantissa := state.mantissa + 1, exponent := state.exponent } := by
    simp only [toReal]
    exact mul_lt_mul_of_pos_right (by norm_num) hstep
  have hupper := (inbetween_bounds hordered hl).2
  have hsuccPos : (0 : ℝ) < state.mantissa + 1 := by
    have : 0 < ((state.mantissa + 1 : ℤ) : ℝ) * bpow β state.exponent := by
      simpa [toReal] using hx.trans hupper
    norm_num only [Int.cast_add, Int.cast_one] at this
    exact pos_of_mul_pos_left this hstep.le
  have hsuccPosZ : (0 : ℤ) < state.mantissa + 1 := by exact_mod_cast hsuccPos
  linarith

/--
For a positive input and a bracket with sufficient precision, the lower mantissa's digit count
determines the canonical exponent. This is
the representation-level counterpart of Flocq's `cexp_inbetween_float`.
-/
theorem cexp_eq_fexp_digits_of_brackets
    {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]
    (state : TruncationState) {x : ℝ} (hx : 0 < x) (hl : state.Brackets β x)
    (hexp : state.exponent ≤ cexp β fexp x ∨
      state.exponent ≤ fexp ((digits β state.mantissa : ℕ) + state.exponent)) :
    cexp β fexp x =
      fexp ((digits β state.mantissa : ℕ) + state.exponent) := by
  have hstep : 0 < bpow β state.exponent := bpow.pos β state.exponent
  have hordered :
      toReal (β := β) { mantissa := state.mantissa, exponent := state.exponent } <
        toReal (β := β) { mantissa := state.mantissa + 1, exponent := state.exponent } := by
    simp only [toReal]
    exact mul_lt_mul_of_pos_right (by norm_num) hstep
  have hbounds := inbetween_bounds hordered hl
  have hmNonneg := state.mantissa_nonneg_of_brackets β hx hl
  rcases hmNonneg.eq_or_lt with hmZero | hmPos
  · have hmZero' : state.mantissa = 0 := hmZero.symm
    have hmagLe : magnitude β x ≤ state.exponent := by
      apply magnitude_le_of_abs_lt_bpow β x state.exponent hx.ne'
      simpa [hmZero', toReal, abs_of_pos hx] using hbounds.2
    change fexp (magnitude β x) =
      fexp ((digits β state.mantissa : ℕ) + state.exponent)
    simp only [hmZero', digits_zero, Nat.cast_zero, zero_add]
    rcases hexp with hcexp | htarget
    · have hsmall : magnitude β x ≤ fexp (magnitude β x) :=
        hmagLe.trans hcexp
      exact (((ValidExp.flocq_valid (fexp := fexp) (magnitude β x)).2
        hsmall).2 state.exponent hcexp).symm
    · have htarget' : state.exponent ≤ fexp state.exponent := by
        simpa [hmZero'] using htarget
      exact ((ValidExp.flocq_valid (fexp := fexp) state.exponent).2 htarget').2
        (magnitude β x) (hmagLe.trans htarget')
  · have hmR : (0 : ℝ) < state.mantissa := by exact_mod_cast hmPos
    have hlowerPos : 0 < toReal (β := β)
        { mantissa := state.mantissa, exponent := state.exponent } := by
      simp only [toReal]
      exact mul_pos hmR hstep
    have hmagLower :
        (digits β state.mantissa : ℤ) + state.exponent ≤ magnitude β x := by
      have hmono := magnitude_mono_pos β hlowerPos hbounds.1
      change magnitude β
        ((state.mantissa : ℝ) * bpow β state.exponent) ≤ magnitude β x at hmono
      rw [magnitude_mul_bpow β (state.mantissa : ℝ) state.exponent
        (by exact_mod_cast (ne_of_gt hmPos)), magnitude_intCast_of_pos β hmPos] at hmono
      exact hmono
    have hupperPower :
        toReal (β := β)
            { mantissa := state.mantissa + 1, exponent := state.exponent } ≤
          bpow β ((digits β state.mantissa : ℤ) + state.exponent) := by
      simp only [toReal, bpow.add_exp]
      exact mul_le_mul_of_nonneg_right
        (intCast_add_one_le_bpow_digits β hmPos) hstep.le
    have hmagUpper : magnitude β x ≤
        (digits β state.mantissa : ℤ) + state.exponent := by
      apply magnitude_le_of_abs_lt_bpow β x _ hx.ne'
      simpa [abs_of_pos hx] using hbounds.2.trans_le hupperPower
    have hmag : magnitude β x =
        (digits β state.mantissa : ℤ) + state.exponent :=
      le_antisymm hmagUpper hmagLower
    simp [cexp, hmag]

/-- A bracket stored at the canonical exponent is a unit bracket for the scaled mantissa. -/
theorem TruncationState.scaledBrackets_of_exponent_eq
    {β : Numerics.Radix} {fexp : ℤ → ℤ}
    (state : TruncationState) {x : ℝ}
    (hl : state.Brackets β x) (hexponent : state.exponent = cexp β fexp x) :
    InbetweenInt state.mantissa (scaledMantissa β fexp x) state.location := by
  rcases state with ⟨mantissa, exponent, location⟩
  have hp : 0 < bpow β exponent := bpow.pos β exponent
  have hp0 : bpow β exponent ≠ 0 := ne_of_gt hp
  rw [scaledMantissa_eq_div, ← hexponent]
  cases hl with
  | exact hx =>
      apply Inbetween.exact
      rw [hx]
      simp [toReal, hp0]
  | inexact order hx hmid =>
      apply Inbetween.inexact order
      · constructor
        · apply (lt_div_iff₀ hp).2
          simpa [toReal] using hx.1
        · apply (div_lt_iff₀ hp).2
          simpa [toReal] using hx.2
      · cases order with
        | lt =>
            rw [cmp_eq_lt_iff] at hmid ⊢
            change x < ((mantissa : ℝ) * bpow β exponent +
              ((mantissa + 1 : ℤ) : ℝ) * bpow β exponent) / 2 at hmid
            change x / bpow β exponent <
              ((mantissa : ℝ) + ((mantissa + 1 : ℤ) : ℝ)) / 2
            calc
              x / bpow β exponent <
                  (((mantissa : ℝ) * bpow β exponent +
                    ((mantissa + 1 : ℤ) : ℝ) * bpow β exponent) / 2) /
                    bpow β exponent := div_lt_div_of_pos_right hmid hp
              _ = ((mantissa : ℝ) + ((mantissa + 1 : ℤ) : ℝ)) / 2 := by
                field_simp
        | eq =>
            rw [cmp_eq_eq_iff] at hmid ⊢
            change x = ((mantissa : ℝ) * bpow β exponent +
              ((mantissa + 1 : ℤ) : ℝ) * bpow β exponent) / 2 at hmid
            change x / bpow β exponent =
              ((mantissa : ℝ) + ((mantissa + 1 : ℤ) : ℝ)) / 2
            calc
              x / bpow β exponent =
                  (((mantissa : ℝ) * bpow β exponent +
                    ((mantissa + 1 : ℤ) : ℝ) * bpow β exponent) / 2) /
                    bpow β exponent := congrArg (fun y => y / bpow β exponent) hmid
              _ = ((mantissa : ℝ) + ((mantissa + 1 : ℤ) : ℝ)) / 2 := by
                field_simp
        | gt =>
            rw [cmp_eq_gt_iff] at hmid ⊢
            change ((mantissa : ℝ) * bpow β exponent +
              ((mantissa + 1 : ℤ) : ℝ) * bpow β exponent) / 2 < x at hmid
            change ((mantissa : ℝ) + ((mantissa + 1 : ℤ) : ℝ)) / 2 <
              x / bpow β exponent
            calc
              ((mantissa : ℝ) + ((mantissa + 1 : ℤ) : ℝ)) / 2 =
                  (((mantissa : ℝ) * bpow β exponent +
                    ((mantissa + 1 : ℤ) : ℝ) * bpow β exponent) / 2) /
                    bpow β exponent := by
                field_simp
              _ < x / bpow β exponent := div_lt_div_of_pos_right hmid hp

/--
Discard `shift` low radix digits and transfer their information into the refined location.
Positive shifts are the intended use; correctness theorems state that premise explicitly.
-/
def truncateAux (β : Numerics.Radix) (state : TruncationState)
    (shift : ℤ) : TruncationState :=
  let power := intPower β shift
  let remainder := state.mantissa % power
  { mantissa := state.mantissa / power
    exponent := state.exponent + shift
    location := refineLocation power remainder state.location }

/-- A positive shift produces a radix power strictly larger than one. -/
theorem intPower_one_lt (β : Numerics.Radix) {shift : ℤ} (hshift : 0 < shift) :
    1 < intPower β shift := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hshift.le
  subst shift
  cases n with
  | zero => simp at hshift
  | succ n =>
      rw [intPower_of_nonneg β (Int.natCast_nonneg _)]
      simp only [Int.toNat_natCast, pow_succ]
      have hbase : 2 ≤ β.base := β.base_valid
      have hpow : 0 < β.base ^ n := pow_pos (Nat.zero_lt_of_lt hbase) n
      exact Int.ofNat_lt.mpr (show 1 < β.base ^ n * β.base by nlinarith)

/-- The truncated remainder is a valid cell index in the discarded radix block. -/
theorem truncateAux_remainder_bounds (β : Numerics.Radix)
    (state : TruncationState) {shift : ℤ} (hshift : 0 < shift) :
    let power := intPower β shift
    0 ≤ state.mantissa % power ∧ state.mantissa % power < power := by
  dsimp only
  have hpower : 0 < intPower β shift := lt_trans Int.zero_lt_one
    (intPower_one_lt β hshift)
  exact ⟨Int.emod_nonneg _ hpower.ne', Int.emod_lt_of_pos _ hpower⟩

/-- Mantissa reconstruction after one truncation step. -/
theorem truncateAux_mantissa_decomposition (β : Numerics.Radix)
    (state : TruncationState) {shift : ℤ} (hshift : 0 < shift) :
    state.mantissa =
      state.mantissa % intPower β shift +
        intPower β shift * (truncateAux β state shift).mantissa := by
  have hpower : intPower β shift ≠ 0 := ne_of_gt
    (lt_trans Int.zero_lt_one (intPower_one_lt β hshift))
  simpa [truncateAux, add_comm] using
    (Int.emod_add_mul_ediv state.mantissa (intPower β shift)).symm

/-- After a positive truncation step, the enlarged bracket still contains the input. -/
theorem truncateAux_brackets (β : Numerics.Radix) (state : TruncationState)
    {shift : ℤ} (hshift : 0 < shift) {x : ℝ}
    (hl : state.Brackets β x) :
    (truncateAux β state shift).Brackets β x := by
  let power := intPower β shift
  let quotient := state.mantissa / power
  let remainder := state.mantissa % power
  let step := bpow β state.exponent
  let start := (quotient : ℝ) * bpow β (state.exponent + shift)
  have hpowerOne : 1 < power := intPower_one_lt β hshift
  have hpowerPos : 0 < power := lt_trans Int.zero_lt_one hpowerOne
  have hpowerReal : (power : ℝ) = bpow β shift := by
    exact intPower_cast_eq_bpow β hshift.le
  have hrem := truncateAux_remainder_bounds β state hshift
  have hdecomp := truncateAux_mantissa_decomposition β state hshift
  have hdecomp' : state.mantissa = remainder + power * quotient := by
    simpa [power, quotient, remainder, truncateAux] using hdecomp
  have hstepPos : 0 < step := bpow.pos β state.exponent
  have hlower :
      start + (remainder : ℝ) * step =
        toReal (β := β) {
          mantissa := state.mantissa
          exponent := state.exponent } := by
    unfold start step toReal
    rw [bpow.add_exp, ← hpowerReal]
    rw [hdecomp', Int.cast_add, Int.cast_mul]
    ring
  have hupper :
      start + ((remainder + 1 : ℤ) : ℝ) * step =
        toReal (β := β) {
          mantissa := state.mantissa + 1
          exponent := state.exponent } := by
    unfold start step
    change
      (quotient : ℝ) * bpow β (state.exponent + shift) +
          ((remainder + 1 : ℤ) : ℝ) * bpow β state.exponent =
        ((state.mantissa + 1 : ℤ) : ℝ) * bpow β state.exponent
    rw [bpow.add_exp, ← hpowerReal]
    rw [hdecomp']
    norm_num only [Int.cast_add, Int.cast_mul, Int.cast_one]
    ring
  have hglobalLower :
      start = toReal (β := β) {
        mantissa := quotient
        exponent := state.exponent + shift } := by
    rfl
  have hglobalUpper :
      start + (power : ℝ) * step =
        toReal (β := β) {
          mantissa := quotient + 1
          exponent := state.exponent + shift } := by
    unfold start step toReal
    rw [bpow.add_exp, ← hpowerReal]
    rw [Int.cast_add, Int.cast_one]
    ring
  have hlCell : Inbetween
      (start + (remainder : ℝ) * step)
      (start + ((remainder + 1 : ℤ) : ℝ) * step)
      x state.location := by
    rw [hlower, hupper]
    exact hl
  have hrefined := refineLocation_correct
    (start := start) (step := step) (steps := power) (k := remainder)
    hstepPos hpowerOne hrem hlCell
  have hglobalUpper' :
      toReal (β := β) {
          mantissa := quotient
          exponent := state.exponent + shift } +
          (power : ℝ) * step =
        toReal (β := β) {
          mantissa := quotient + 1
          exponent := state.exponent + shift } := by
    rw [← hglobalLower]
    exact hglobalUpper
  rw [hglobalLower, hglobalUpper'] at hrefined
  change Inbetween
    (toReal (β := β) {
      mantissa := (truncateAux β state shift).mantissa
      exponent := (truncateAux β state shift).exponent })
    (toReal (β := β) {
      mantissa := (truncateAux β state shift).mantissa + 1
      exponent := (truncateAux β state shift).exponent })
    x (truncateAux β state shift).location
  simpa [truncateAux, power, quotient, remainder] using hrefined

/-- Number of low radix digits discarded to reach the exponent selected by `fexp`. -/
def truncationShift (β : Numerics.Radix) (fexp : ℤ → ℤ)
    (state : TruncationState) : ℤ :=
  fexp ((digits β state.mantissa : ℕ) + state.exponent) - state.exponent

/-- Truncate only when the target exponent lies strictly above the stored exponent. -/
def truncate (β : Numerics.Radix) (fexp : ℤ → ℤ)
    (state : TruncationState) : TruncationState :=
  let shift := truncationShift β fexp state
  if 0 < shift then truncateAux β state shift else state

/-- Format-driven truncation preserves the bracketing relation for the input. -/
theorem truncate_brackets (β : Numerics.Radix) (fexp : ℤ → ℤ)
    (state : TruncationState) {x : ℝ} (hl : state.Brackets β x) :
    (truncate β fexp state).Brackets β x := by
  by_cases hshift : 0 < truncationShift β fexp state
  · rw [truncate, ite_eq_left hshift]
    exact truncateAux_brackets β state hshift hl
  · rw [truncate, ite_eq_right hshift]
    exact hl

/--
For a positive input with sufficient initial precision, truncation both preserves the bracket and
selects the canonical format exponent.
-/
theorem truncate_brackets_and_exponent
    {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]
    (state : TruncationState) {x : ℝ} (hx : 0 < x) (hl : state.Brackets β x)
    (hexp : state.exponent ≤ cexp β fexp x ∨
      state.exponent ≤ fexp ((digits β state.mantissa : ℕ) + state.exponent)) :
    (truncate β fexp state).Brackets β x ∧
      (truncate β fexp state).exponent = cexp β fexp x := by
  have hcanonical := cexp_eq_fexp_digits_of_brackets state hx hl hexp
  constructor
  · exact truncate_brackets β fexp state hl
  · by_cases hshift : 0 < truncationShift β fexp state
    · rw [truncate, ite_eq_left hshift]
      simp only [truncateAux, truncationShift]
      linarith
    · rw [truncate, ite_eq_right hshift]
      simp only [truncationShift] at hshift
      have hle : state.exponent ≤ cexp β fexp x := by
        rcases hexp with h | h
        · exact h
        · rw [hcanonical]
          exact h
      rw [hcanonical] at hle ⊢
      linarith

/-- Nearest-even result selected from a format-truncated bracket. -/
def roundTruncatedNearestEven
    (β : Numerics.Radix) (fexp : ℤ → ℤ) (state : TruncationState) : FloatRep β :=
  let truncated := truncate β fexp state
  { mantissa := conditionalIncrement
      (roundNearestLocation nearestEvenChoice
        truncated.mantissa truncated.location) truncated.mantissa
    exponent := truncated.exponent }

/-- Truncation never changes a zero mantissa into a nonzero one. -/
@[simp] theorem truncate_zero_mantissa (β : Numerics.Radix) (fexp : ℤ → ℤ)
    (exponent : ℤ) (location : Location) :
    (truncate β fexp {
      mantissa := 0, exponent := exponent, location := location }).mantissa = 0 := by
  simp only [truncate, truncationShift, digits_zero, Nat.cast_zero,
    zero_add, sub_pos]
  split_ifs
  · simp [truncateAux]
  · rfl

section GenericFormat

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-- Rounded mantissa paired with the input's canonical exponent. -/
noncomputable def roundedFloat (rnd : ℝ → ℤ) (x : ℝ) : FloatRep β :=
  { mantissa := rnd (scaledMantissa β fexp x)
    exponent := cexp β fexp x }

omit [ValidExp fexp] in
/--
A rounded scaled mantissa and the input's canonical exponent represent the rounded real value.
-/
theorem round_eq_toReal_of_scaled_round_eq (rnd : ℝ → ℤ) (x : ℝ) (mantissa : ℤ)
    (hmantissa : rnd (scaledMantissa β fexp x) = mantissa) :
    round (β := β) (fexp := fexp) rnd x =
      toReal (β := β) {
        mantissa := mantissa
        exponent := cexp β fexp x } := by
  simp [round, toReal, hmantissa]

omit [ValidExp fexp] in
/-- A scaled-mantissa bracket computes format-level downward rounding. -/
theorem round_floor_of_scaledBracket (x : ℝ) {m : ℤ} {location : Location}
    (hl : InbetweenInt m (scaledMantissa β fexp x) location) :
    round (β := β) (fexp := fexp) floorRound x =
      toReal (β := β) {
        mantissa := m
        exponent := cexp β fexp x } := by
  apply round_eq_toReal_of_scaled_round_eq
  exact inbetweenInt_floor hl

omit [ValidExp fexp] in
/-- A scaled-mantissa bracket computes format-level upward rounding. -/
theorem round_ceil_of_scaledBracket (x : ℝ) {m : ℤ} {location : Location}
    (hl : InbetweenInt m (scaledMantissa β fexp x) location) :
    round (β := β) (fexp := fexp) ceilRound x =
      toReal (β := β) {
        mantissa := conditionalIncrement (roundUpLocation location) m
        exponent := cexp β fexp x } := by
  apply round_eq_toReal_of_scaled_round_eq
  exact inbetweenInt_ceil hl

omit [ValidExp fexp] in
/-- A scaled-mantissa bracket computes format-level nearest-even rounding. -/
theorem round_nearestEven_of_scaledBracket (x : ℝ) {m : ℤ}
    {location : Location}
    (hl : InbetweenInt m (scaledMantissa β fexp x) location) :
    round (β := β) (fexp := fexp) nearestEven x =
      toReal (β := β) {
        mantissa := conditionalIncrement
          (roundNearestLocation nearestEvenChoice m location) m
        exponent := cexp β fexp x } := by
  apply round_eq_toReal_of_scaled_round_eq
  exact inbetweenInt_nearestEven hl

/-- Nearest-even integer selected from the real input's floor bracket. -/
noncomputable def nearestEvenMantissa (x : ℝ) : ℤ :=
  conditionalIncrement
    (roundNearestLocation nearestEvenChoice ⌊x⌋ (integerLocation x)) ⌊x⌋

omit [ValidExp fexp] in
/-- Nearest-even format rounding agrees with selection from the scaled input's floor bracket. -/
theorem round_nearestEven_computed (x : ℝ) :
    round (β := β) (fexp := fexp) nearestEven x =
      toReal (β := β) {
        mantissa := nearestEvenMantissa (scaledMantissa β fexp x)
        exponent := cexp β fexp x } := by
  exact round_nearestEven_of_scaledBracket x
    (integerLocation_spec (scaledMantissa β fexp x))

/--
Nearest-even selection after canonical truncation agrees with generic rounded-real semantics.
-/
theorem roundTruncatedNearestEven_correct
    (state : TruncationState) {x : ℝ} (hx : 0 < x) (hl : state.Brackets β x)
    (hexp : state.exponent ≤ cexp β fexp x ∨
      state.exponent ≤ fexp ((digits β state.mantissa : ℕ) + state.exponent)) :
    toReal (roundTruncatedNearestEven β fexp state) =
      round (β := β) (fexp := fexp) nearestEven x := by
  let truncated := truncate β fexp state
  have ht := truncate_brackets_and_exponent state hx hl hexp
  have hs : InbetweenInt truncated.mantissa
      (scaledMantissa β fexp x) truncated.location :=
    truncated.scaledBrackets_of_exponent_eq ht.1 ht.2
  have hr := round_nearestEven_of_scaledBracket (β := β) (fexp := fexp) x hs
  rw [hr]
  simp [roundTruncatedNearestEven, truncated, ht.2]

end GenericFormat

end FloatLib.Floats.Formats.Flocq
