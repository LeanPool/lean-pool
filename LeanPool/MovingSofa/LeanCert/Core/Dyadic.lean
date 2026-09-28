/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
/-!
# Dyadic Rationals (n * 2^e)

This file defines Dyadic rationals, which are the backbone of high-performance
verified numerics. Unlike arbitrary `Rat`, Dyadics do not require GCD
normalization, making them significantly faster for kernel evaluation.

## Main definitions

* `Dyadic` - A dyadic rational number: `mantissa * 2^exponent`
* `Dyadic.toRat` - Convert to standard rational
* `Dyadic.add`, `Dyadic.mul`, `Dyadic.neg` - Arithmetic operations
* `Dyadic.shiftDown`, `Dyadic.shiftUp` - Directed rounding for interval bounds

## Design notes

Dyadics use power-of-2 multiplications instead of GCD-based normalization.
This makes them orders of magnitude faster for kernel evaluation via
`native_decide`, since 2^n can be computed by simple bit operations.

For interval arithmetic, we use directed rounding:
- Lower bounds use `shiftDown` (round toward -∞)
- Upper bounds use `shiftUp` (round toward +∞)

This ensures mathematical soundness even when truncating precision.
-/

@[expose] public section

namespace LeanCert.Core

/-- A Dyadic rational number: `mantissa * 2^exponent`

This representation allows fast arithmetic without GCD normalization. -/
structure Dyadic where
  /-- The significand/mantissa -/
  mantissa : Int
  /-- The exponent (power of 2) -/
  exponent : Int
  deriving Repr, DecidableEq, Inhabited

namespace Dyadic

/-! ### Helper: Power of 2 -/

/-- Compute 2^n for natural n -/
def pow2Nat (n : Nat) : Nat := Nat.shiftLeft 1 n

/-- Shift an integer left by n bits (multiply by 2^n) -/
def shiftLeftInt (m : Int) (n : Nat) : Int :=
  m * (pow2Nat n : Int)

/-- Shift an integer right by n bits (divide by 2^n, floor toward -∞) -/
def shiftRightInt (m : Int) (n : Nat) : Int :=
  m / (pow2Nat n : Int)

/-- Check if any of the low n bits are set -/
def hasLowBits (m : Int) (n : Nat) : Bool :=
  m % (pow2Nat n : Int) ≠ 0

/-! ### Conversion to Rat -/

/-- Convert Dyadic to standard Rat.

For non-negative exponents: `mantissa * 2^exponent`
For negative exponents: `mantissa / 2^(-exponent)` -/
def toRat (d : Dyadic) : ℚ :=
  if d.exponent ≥ 0 then
    d.mantissa * (pow2Nat d.exponent.toNat : ℤ)
  else
    (d.mantissa : ℚ) / (pow2Nat (-d.exponent).toNat : ℕ)

instance : Coe Dyadic ℚ where coe := toRat

/-- Equality of represented values, ignoring noncanonical mantissa/exponent pairs. -/
def ValueEq (d₁ d₂ : Dyadic) : Prop := d₁.toRat = d₂.toRat

instance (d₁ d₂ : Dyadic) : Decidable (d₁.ValueEq d₂) :=
  inferInstanceAs (Decidable (d₁.toRat = d₂.toRat))

instance : Setoid Dyadic where
  r := ValueEq
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

@[simp] theorem valueEq_iff (d₁ d₂ : Dyadic) :
    d₁.ValueEq d₂ ↔ d₁.toRat = d₂.toRat := Iff.rfl

/-- A lawful identity key for caches, sets, serialization, and deduplication.

Arithmetic keeps the fast, noncanonical `Dyadic` representation. Converting at
an identity boundary collapses all representations of the same rational value.
-/
structure CanonicalKey where
  /-- The exact rational value used to compare normalized dyadic numbers. -/
  value : ℚ
  deriving Repr, DecidableEq, BEq, Hashable

/-- Convert a dyadic value to its canonical identity key. -/
def canonicalKey (d : Dyadic) : CanonicalKey := ⟨d.toRat⟩

@[simp] theorem canonicalKey_value (d : Dyadic) : d.canonicalKey.value = d.toRat := rfl

/-- Canonical keys agree exactly when represented dyadic values agree. -/
theorem canonicalKey_eq_iff (d₁ d₂ : Dyadic) :
    d₁.canonicalKey = d₂.canonicalKey ↔ d₁.ValueEq d₂ := by
  simp only [canonicalKey, ValueEq, CanonicalKey.mk.injEq]

/-- Cast a Dyadic to ℝ by going through ℚ -/
def toReal (d : Dyadic) : ℝ := Rat.cast (toRat d)

instance : Coe Dyadic ℝ where coe := toReal

/-- Equality of rational denotations gives semantic dyadic equality. -/
theorem valueEq_of_toRat_eq {d₁ d₂ : Dyadic}
    (h : d₁.toRat = d₂.toRat) : d₁.ValueEq d₂ := h

/-! ### Construction -/

/-- Create a dyadic from an integer (exponent = 0) -/
def ofInt (i : Int) : Dyadic := ⟨i, 0⟩

/-- Create a dyadic for 2^n -/
def pow2 (n : Int) : Dyadic := ⟨1, n⟩

/-- Zero as a Dyadic -/
def zero : Dyadic := ⟨0, 0⟩

/-- One as a Dyadic -/
def one : Dyadic := ⟨1, 0⟩

instance : Zero Dyadic where zero := Dyadic.zero
instance : One Dyadic where one := Dyadic.one

theorem toRat_ofInt (i : Int) : (ofInt i).toRat = i := by
  simp only [ofInt, toRat, pow2Nat, Int.toNat_zero, le_refl, ↓reduceIte]
  have h : Nat.shiftLeft 1 0 = 1 := rfl
  simp only [h, Nat.cast_one, Int.cast_one, mul_one]

@[simp]
theorem toRat_zero : (0 : Dyadic).toRat = 0 := by
  have h := toRat_ofInt 0; rw [Int.cast_zero] at h; exact h

@[simp]
theorem toRat_one : (1 : Dyadic).toRat = 1 := by
  have h := toRat_ofInt 1; rw [Int.cast_one] at h; exact h

/-! ### Arithmetic Operations -/

/-- Negation of a Dyadic -/
def neg (d : Dyadic) : Dyadic := ⟨-d.mantissa, d.exponent⟩

instance : Neg Dyadic where neg := Dyadic.neg

/-- Addition of Dyadics. Aligns exponents by shifting the mantissa with
larger exponent to match the smaller one. -/
def add (d₁ d₂ : Dyadic) : Dyadic :=
  if d₁.exponent ≤ d₂.exponent then
    let shift := (d₂.exponent - d₁.exponent).toNat
    ⟨d₁.mantissa + shiftLeftInt d₂.mantissa shift, d₁.exponent⟩
  else
    let shift := (d₁.exponent - d₂.exponent).toNat
    ⟨shiftLeftInt d₁.mantissa shift + d₂.mantissa, d₂.exponent⟩

instance : Add Dyadic where add := Dyadic.add

/-- Subtraction of Dyadics -/
def sub (d₁ d₂ : Dyadic) : Dyadic := add d₁ (neg d₂)

instance : Sub Dyadic where sub := Dyadic.sub

/-- Multiplication of Dyadics. Simply multiplies mantissas and adds exponents. -/
def mul (d₁ d₂ : Dyadic) : Dyadic :=
  ⟨d₁.mantissa * d₂.mantissa, d₁.exponent + d₂.exponent⟩

instance : Mul Dyadic where mul := Dyadic.mul

/-- Absolute value of a Dyadic -/
def abs (d : Dyadic) : Dyadic := ⟨Int.natAbs d.mantissa, d.exponent⟩

/-- Scale by a power of 2 (efficient: just adjusts exponent) -/
def scale2 (d : Dyadic) (n : Int) : Dyadic := ⟨d.mantissa, d.exponent + n⟩

/-! ### Directed Rounding for Interval Arithmetic -/

/-- Shift a dyadic to a new (larger) exponent with "Down" rounding (for lower bounds).

If `newExp > d.exponent`, we lose precision by right-shifting the mantissa.
Bits are discarded (floor division toward -∞). -/
def shiftDown (d : Dyadic) (newExp : Int) : Dyadic :=
  if newExp ≤ d.exponent then
    d -- already at or below target precision
  else
    let diff := (newExp - d.exponent).toNat
    -- Integer division is floor division toward -∞ for positive divisor
    ⟨shiftRightInt d.mantissa diff, newExp⟩

/-- Shift a dyadic to a new (larger) exponent with "Up" rounding (for upper bounds).

If `newExp > d.exponent`, we lose precision by right-shifting the mantissa.
If any bits are lost, we add 1 to ensure upward rounding (ceiling toward +∞). -/
def shiftUp (d : Dyadic) (newExp : Int) : Dyadic :=
  if newExp ≤ d.exponent then
    d -- already at or below target precision
  else
    let diff := (newExp - d.exponent).toNat
    if hasLowBits d.mantissa diff then
      -- Lost bits: round up
      ⟨shiftRightInt d.mantissa diff + 1, newExp⟩
    else
      -- No lost bits: exact
      ⟨shiftRightInt d.mantissa diff, newExp⟩

/-! ### Normalization (Mantissa Control) -/

/-- Get the bit length of a natural number -/
def natBitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

/-- Get the bit length of the absolute value of an integer -/
def bitLength (m : Int) : Nat := natBitLength m.natAbs

/-- Normalize a Dyadic to keep the mantissa within a reasonable bit-limit.

This prevents mantissas from growing without bound during repeated multiplications.
Similar to how hardware floats work, but with directed rounding.

- `maxBits`: Maximum allowed bits for mantissa (default 256)
- `roundUp`: If true, round toward +∞; if false, round toward -∞ -/
def normalize (d : Dyadic) (maxBits : Nat := 256) (roundUp : Bool := false) : Dyadic :=
  let bits := bitLength d.mantissa
  if bits ≤ maxBits then d
  else
    let shift := bits - maxBits
    let newExp := d.exponent + shift
    if roundUp then shiftUp d newExp
    else shiftDown d newExp

/-- Normalize for lower bounds (round down) -/
def normalizeDown (d : Dyadic) (maxBits : Nat := 256) : Dyadic :=
  normalize d maxBits false

/-- Normalize for upper bounds (round up) -/
def normalizeUp (d : Dyadic) (maxBits : Nat := 256) : Dyadic :=
  normalize d maxBits true

/-! ### Comparison -/

/-- Compare two Dyadics (decidable) -/
def compare (d₁ d₂ : Dyadic) : Ordering :=
  -- Align to smaller exponent for comparison
  if d₁.exponent ≤ d₂.exponent then
    let shift := (d₂.exponent - d₁.exponent).toNat
    Ord.compare d₁.mantissa (shiftLeftInt d₂.mantissa shift)
  else
    let shift := (d₁.exponent - d₂.exponent).toNat
    Ord.compare (shiftLeftInt d₁.mantissa shift) d₂.mantissa

instance : Ord Dyadic where compare := Dyadic.compare

/-- Less-than-or-equal for Dyadics -/
def le (d₁ d₂ : Dyadic) : Bool := compare d₁ d₂ != .gt

/-- Less-than for Dyadics -/
def lt (d₁ d₂ : Dyadic) : Bool := compare d₁ d₂ == .lt

instance : LE Dyadic where le d₁ d₂ := le d₁ d₂
instance : LT Dyadic where lt d₁ d₂ := lt d₁ d₂

instance : DecidableRel (α := Dyadic) (· ≤ ·) := fun d₁ d₂ =>
  if h : le d₁ d₂ then isTrue h else isFalse h

instance : DecidableRel (α := Dyadic) (· < ·) := fun d₁ d₂ =>
  if h : lt d₁ d₂ then isTrue h else isFalse h

/-- Minimum of two Dyadics -/
def min (d₁ d₂ : Dyadic) : Dyadic := if le d₁ d₂ then d₁ else d₂

/-- Maximum of two Dyadics -/
def max (d₁ d₂ : Dyadic) : Dyadic := if le d₁ d₂ then d₂ else d₁

/-- Minimum of four Dyadics -/
def min4 (a b c d : Dyadic) : Dyadic := min (min a b) (min c d)

/-- Maximum of four Dyadics -/
def max4 (a b c d : Dyadic) : Dyadic := max (max a b) (max c d)

/-! ### Correctness Theorems -/

/-! #### Helper lemmas for shift proofs -/

/-- shiftRightInt is floor division by 2^n -/
private theorem shiftRightInt_eq_div (m : Int) (n : Nat) :
    shiftRightInt m n = m / (pow2Nat n : Int) := by
  simp only [shiftRightInt, pow2Nat]

/-- shiftLeftInt is multiplication by 2^n -/
private theorem shiftLeftInt_eq_mul (m : Int) (n : Nat) :
    shiftLeftInt m n = m * (pow2Nat n : Int) := by
  simp only [shiftLeftInt, pow2Nat]

/-- pow2Nat n is always positive.
    Proof: 2^n ≥ 1 for all n. -/
private theorem pow2Nat_pos (n : Nat) : 0 < pow2Nat n := by
  unfold pow2Nat
  -- Use the fact that shiftLeft 1 n = 2^n
  conv => lhs; rw [show (0 : ℕ) = 0 from rfl]
  conv => rhs; rw [show Nat.shiftLeft 1 n = 1 * 2^n from Nat.shiftLeft_eq 1 n]
  simp only [one_mul]
  exact Nat.one_le_two_pow

/-- pow2Nat as Int is positive -/
private theorem pow2Nat_int_pos (n : Nat) : (0 : Int) < (pow2Nat n : Int) := by
  exact Int.natCast_pos.mpr (pow2Nat_pos n)

/-- Floor division property: (m / d) * d ≤ m for positive d.
    Follows from m % d ≥ 0 and m = m % d + d * (m / d). -/
private theorem int_ediv_mul_le (m : Int) (d : Int) (hd : 0 < d) :
    (m / d) * d ≤ m := Int.ediv_mul_le m (ne_of_gt hd)

/-- Ceiling division property: m ≤ (m / d + 1) * d when m % d ≠ 0 -/
private theorem int_ediv_add_one_mul_ge (m : Int) (d : Int) (hd : 0 < d) (_hrem : m % d ≠ 0) :
    m ≤ (m / d + 1) * d := by
  -- From Int.emod_add_mul_ediv: m % d + d * (m / d) = m
  have h := Int.emod_add_mul_ediv m d
  -- m % d < d since d > 0
  have hlt := Int.emod_lt_of_pos m hd
  -- d + d * (m / d) = (m / d + 1) * d
  have heq : d + d * (m / d) = (m / d + 1) * d := by
    rw [add_mul, one_mul, mul_comm d (m / d), add_comm]
  -- m = m % d + d * (m / d) < d + d * (m / d) = (m / d + 1) * d
  have hcalc : m < (m / d + 1) * d :=
    calc m = m % d + d * (m / d) := h.symm
      _ < d + d * (m / d) := by gcongr 1
      _ = (m / d + 1) * d := heq
  exact le_of_lt hcalc

/-- Exact division: m = (m / d) * d when m % d = 0 -/
private theorem int_ediv_mul_eq (m : Int) (d : Int) (_hd : 0 < d) (hrem : m % d = 0) :
    (m / d) * d = m := by
  -- From Int.emod_add_mul_ediv: m % d + d * (m / d) = m
  have h := Int.emod_add_mul_ediv m d
  -- Since m % d = 0, we have d * (m / d) = m
  simp only [hrem, zero_add] at h
  -- d * (m / d) = m, so (m / d) * d = m
  calc (m / d) * d = d * (m / d) := mul_comm _ _
    _ = m := h

theorem toRat_neg (d : Dyadic) : (neg d).toRat = -(d.toRat) := by
  by_cases h : d.exponent ≥ 0
  · simp [neg, toRat, h]
  · simp only [toRat, neg, ge_iff_le, h, ↓reduceIte, Int.cast_neg]
    rw [neg_div]

/-! ### Arithmetic Homomorphisms -/

/-- Helper: pow2Nat n = 2^n -/
private theorem pow2Nat_eq_pow (n : Nat) : pow2Nat n = 2 ^ n := by
  unfold pow2Nat
  rw [show Nat.shiftLeft 1 n = 1 * 2^n from Nat.shiftLeft_eq 1 n]
  simp only [one_mul]

/-- Unification lemma: toRat d = d.mantissa * 2^d.exponent -/
theorem toRat_eq (d : Dyadic) : d.toRat = d.mantissa * (2 : ℚ) ^ d.exponent := by
  unfold toRat
  split_ifs with h
  · -- Case: exponent ≥ 0
    have he : d.exponent = (d.exponent.toNat : ℤ) := (Int.toNat_of_nonneg h).symm
    rw [he, zpow_natCast, pow2Nat_eq_pow]
    -- Simplify (↑n : ℤ).toNat = n
    simp only [Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, Int.cast_ofNat,
               Int.toNat_natCast]
  · -- Case: exponent < 0
    push Not at h
    have hpos : 0 ≤ -d.exponent := Int.neg_nonneg.mpr (le_of_lt h)
    -- (-d.exponent).toNat = the natural number n such that d.exponent = -n
    set n := (-d.exponent).toNat with hn_def
    have hne : d.exponent = -(n : ℤ) := by
      rw [Int.toNat_of_nonneg hpos]; omega
    rw [hne, zpow_neg, zpow_natCast, pow2Nat_eq_pow]
    -- Goal: mantissa / 2^n = mantissa * (2^n)⁻¹
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]

theorem toRat_add (d₁ d₂ : Dyadic) : (add d₁ d₂).toRat = d₁.toRat + d₂.toRat := by
  -- Rewrite using toRat_eq to work with mantissa * 2^exponent form
  rw [toRat_eq d₁, toRat_eq d₂]
  unfold add
  split_ifs with h
  · -- Case: d₁.exponent ≤ d₂.exponent
    rw [toRat_eq]
    simp only [shiftLeftInt, pow2Nat_eq_pow]
    -- Goal: (m₁ + m₂ * 2^shift) * 2^e₁ = m₁ * 2^e₁ + m₂ * 2^e₂
    set shift := (d₂.exponent - d₁.exponent).toNat with hshift_def
    have hshift : (shift : ℤ) = d₂.exponent - d₁.exponent := by
      rw [hshift_def, Int.toNat_of_nonneg]; omega
    -- 2^shift * 2^e₁ = 2^e₂
    have hexp : (2 : ℚ) ^ shift * 2 ^ d₁.exponent = 2 ^ d₂.exponent := by
      have h2 : (2 : ℚ) ^ shift = (2 : ℚ) ^ (shift : ℤ) := by rw [zpow_natCast]
      rw [h2, ← zpow_add₀ (two_ne_zero), hshift]
      congr 1; omega
    -- Show ↑(2^shift : ℕ) = (2 : ℚ)^shift
    have hcast : (↑(2 ^ shift : ℕ) : ℚ) = (2 : ℚ) ^ shift := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    -- Push casts inside and simplify
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hcast, add_mul, mul_assoc, hexp]
  · -- Case: d₁.exponent > d₂.exponent
    rw [toRat_eq]
    simp only [shiftLeftInt, pow2Nat_eq_pow]
    set shift := (d₁.exponent - d₂.exponent).toNat with hshift_def
    have hshift : (shift : ℤ) = d₁.exponent - d₂.exponent := by
      rw [hshift_def, Int.toNat_of_nonneg]; omega
    have hexp : (2 : ℚ) ^ shift * 2 ^ d₂.exponent = 2 ^ d₁.exponent := by
      have h2 : (2 : ℚ) ^ shift = (2 : ℚ) ^ (shift : ℤ) := by rw [zpow_natCast]
      rw [h2, ← zpow_add₀ (two_ne_zero), hshift]
      congr 1; omega
    have hcast : (↑(2 ^ shift : ℕ) : ℚ) = (2 : ℚ) ^ shift := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hcast, add_mul, mul_assoc, hexp,
      add_comm]

theorem toRat_mul (d₁ d₂ : Dyadic) : (mul d₁ d₂).toRat = d₁.toRat * d₂.toRat := by
  -- Key: (m1*m2) * 2^(e1+e2) = (m1*2^e1) * (m2*2^e2)
  rw [toRat_eq d₁, toRat_eq d₂, toRat_eq]
  unfold mul
  simp only [Int.cast_mul]
  -- Goal: (m₁ * m₂) * 2^(e₁ + e₂) = (m₁ * 2^e₁) * (m₂ * 2^e₂)
  -- Use zpow_add₀: 2^(e₁ + e₂) = 2^e₁ * 2^e₂
  rw [zpow_add₀ (two_ne_zero)]
  -- Goal: (a * b) * (c * d) = (a * c) * (b * d)
  -- Use mul_mul_mul_comm: a * b * (c * d) = a * c * (b * d)
  rw [mul_mul_mul_comm]

/-! ### Rounding Properties -/

/-- shiftDown produces a value ≤ the original -/
theorem toRat_shiftDown_le (d : Dyadic) (newExp : Int) :
    (shiftDown d newExp).toRat ≤ d.toRat := by
  simp only [shiftDown]
  split_ifs with h
  · exact le_refl _
  · -- newExp > d.exponent
    push Not at h
    set diff := (newExp - d.exponent).toNat with hdiff_def
    have hdiff : (diff : ℤ) = newExp - d.exponent := by
      rw [hdiff_def, Int.toNat_of_nonneg]; omega
    have hnewExp : newExp = d.exponent + diff := by omega
    rw [toRat_eq, toRat_eq]
    simp only [shiftRightInt, pow2Nat_eq_pow]
    -- Use int_ediv_mul_le: (m / b) * b ≤ m
    have hpow_int_pos : (0 : ℤ) < (2 ^ diff : ℕ) := Int.natCast_pos.mpr (Nat.one_le_two_pow)
    have hdiv : d.mantissa / (2 ^ diff : ℕ) * (2 ^ diff : ℕ) ≤ d.mantissa :=
      int_ediv_mul_le d.mantissa (2 ^ diff : ℕ) hpow_int_pos
    -- Key: 2^newExp = 2^d.exponent * 2^diff
    have hpow : (2 : ℚ) ^ newExp = 2 ^ d.exponent * (2 : ℚ) ^ diff := by
      rw [hnewExp, zpow_add₀ (two_ne_zero), zpow_natCast]
    rw [hpow]
    -- Goal: (m / 2^diff) * (2^d.exp * 2^diff) ≤ m * 2^d.exp
    have hpos : (0 : ℚ) < 2 ^ d.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
    have hpow2_pos : (0 : ℚ) < (2 : ℚ) ^ diff := pow_pos (by norm_num : (0 : ℚ) < 2) _
    -- Convert hdiv to ℚ: (m / 2^diff) * 2^diff ≤ m
    have hq : (↑(d.mantissa / (2 ^ diff : ℕ)) : ℚ) * ((2 : ℚ) ^ diff) ≤ d.mantissa := by
      have heq : ((2 : ℚ) ^ diff) = ((2 ^ diff : ℕ) : ℚ) := by simp
      rw [heq]
      -- Goal: (m/b : ℤ) * (b : ℕ) ≤ m in ℚ
      -- hdiv: (m/b) * b ≤ m in ℤ
      calc (↑(d.mantissa / (2 ^ diff : ℕ)) : ℚ) * ↑(2 ^ diff : ℕ)
          = ↑(d.mantissa / (2 ^ diff : ℕ) * (2 ^ diff : ℕ)) := by simp only [Int.cast_mul,
            Int.cast_natCast]
        _ ≤ ↑d.mantissa := Int.cast_le.mpr hdiv
    -- Rearrange: (m/b) * (c * b) = (m/b) * b * c and apply hq
    have hrearr : (↑(d.mantissa / (2 ^ diff : ℕ)) : ℚ) * (2 ^ d.exponent * (2 : ℚ) ^ diff)
                = (↑(d.mantissa / (2 ^ diff : ℕ))) * ((2 : ℚ) ^ diff) * 2 ^ d.exponent := by
      rw [mul_comm (2 ^ d.exponent) ((2 : ℚ) ^ diff), mul_assoc]
    rw [hrearr]
    exact mul_le_mul_of_nonneg_right hq (le_of_lt hpos)

/-- shiftUp produces a value ≥ the original -/
theorem toRat_shiftUp_ge (d : Dyadic) (newExp : Int) :
    d.toRat ≤ (shiftUp d newExp).toRat := by
  simp only [shiftUp]
  split_ifs with h hlowbits
  · exact le_refl _
  · -- Case: Lost bits, added 1
    push Not at h
    set diff := (newExp - d.exponent).toNat with hdiff_def
    have hdiff : (diff : ℤ) = newExp - d.exponent := by
      rw [hdiff_def, Int.toNat_of_nonneg]; omega
    have hnewExp : newExp = d.exponent + diff := by omega
    rw [toRat_eq, toRat_eq]
    simp only [shiftRightInt, pow2Nat_eq_pow, hasLowBits] at hlowbits ⊢
    -- Use int_ediv_add_one_mul_ge: m ≤ (m/b + 1) * b when m % b ≠ 0
    have hpow_int_pos : (0 : ℤ) < (2 ^ diff : ℕ) := Int.natCast_pos.mpr (Nat.one_le_two_pow)
    have hrem : d.mantissa % (2 ^ diff : ℕ) ≠ 0 := by
      simpa only [ne_eq, decide_eq_true_eq] using hlowbits
    have hceil : d.mantissa ≤ (d.mantissa / (2 ^ diff : ℕ) + 1) * (2 ^ diff : ℕ) :=
      int_ediv_add_one_mul_ge d.mantissa (2 ^ diff : ℕ) hpow_int_pos hrem
    -- Key: 2^newExp = 2^d.exponent * 2^diff
    have hpow : (2 : ℚ) ^ newExp = 2 ^ d.exponent * (2 : ℚ) ^ diff := by
      rw [hnewExp, zpow_add₀ (two_ne_zero), zpow_natCast]
    rw [hpow]
    have hpos : (0 : ℚ) < 2 ^ d.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
    -- Convert hceil to ℚ: m ≤ (m/b + 1) * b
    have hq : (d.mantissa : ℚ) ≤ (↑(d.mantissa / (2 ^ diff : ℕ) + 1)) * ((2 : ℚ) ^ diff) := by
      have heq : ((2 : ℚ) ^ diff) = ((2 ^ diff : ℕ) : ℚ) := by simp
      rw [heq]
      calc (d.mantissa : ℚ) ≤ ↑((d.mantissa / (2 ^ diff : ℕ) + 1) * (2 ^ diff : ℕ)) :=
        Int.cast_le.mpr hceil
        _ = ↑(d.mantissa / (2 ^ diff : ℕ) + 1) * ↑(2 ^ diff : ℕ) := by simp only [Int.cast_mul,
          Int.cast_natCast]
    -- Rearrange and apply hq
    have hrearr : (↑(d.mantissa / (2 ^ diff : ℕ) + 1) : ℚ) * (2 ^ d.exponent * (2 : ℚ) ^ diff)
                = (↑(d.mantissa / (2 ^ diff : ℕ) + 1)) * ((2 : ℚ) ^ diff) * 2 ^ d.exponent := by
      rw [mul_comm (2 ^ d.exponent) ((2 : ℚ) ^ diff), mul_assoc]
    rw [hrearr]
    calc (d.mantissa : ℚ) * 2 ^ d.exponent
        ≤ (↑(d.mantissa / (2 ^ diff : ℕ) + 1) * ((2 : ℚ) ^ diff)) * 2 ^ d.exponent :=
            mul_le_mul_of_nonneg_right hq (le_of_lt hpos)
      _ = ↑(d.mantissa / (2 ^ diff : ℕ) + 1) * (2 : ℚ) ^ diff * 2 ^ d.exponent := by rfl
  · -- Case: No lost bits, exact (equality)
    push Not at h
    set diff := (newExp - d.exponent).toNat with hdiff_def
    have hdiff : (diff : ℤ) = newExp - d.exponent := by
      rw [hdiff_def, Int.toNat_of_nonneg]; omega
    have hnewExp : newExp = d.exponent + diff := by omega
    rw [toRat_eq, toRat_eq]
    simp only [shiftRightInt, pow2Nat_eq_pow, hasLowBits] at hlowbits ⊢
    -- Use int_ediv_mul_eq: (m/b) * b = m when m % b = 0
    have hpow_int_pos : (0 : ℤ) < (2 ^ diff : ℕ) := Int.natCast_pos.mpr (Nat.one_le_two_pow)
    have hrem : d.mantissa % (2 ^ diff : ℕ) = 0 := by
      simp only [ne_eq, decide_eq_true_eq, not_not] at hlowbits; exact hlowbits
    have hexact : (d.mantissa / (2 ^ diff : ℕ)) * (2 ^ diff : ℕ) = d.mantissa :=
      int_ediv_mul_eq d.mantissa (2 ^ diff : ℕ) hpow_int_pos hrem
    -- Key: 2^newExp = 2^d.exponent * 2^diff
    have hpow : (2 : ℚ) ^ newExp = 2 ^ d.exponent * (2 : ℚ) ^ diff := by
      rw [hnewExp, zpow_add₀ (two_ne_zero), zpow_natCast]
    rw [hpow]
    -- Goal: m * 2^exp ≤ (m/b) * (2^exp * 2^diff)
    -- Since (m/b) * b = m, this is equality
    have heq : ((2 : ℚ) ^ diff) = ((2 ^ diff : ℕ) : ℚ) := by simp
    calc (d.mantissa : ℚ) * 2 ^ d.exponent
        = ↑((d.mantissa / (2 ^ diff : ℕ)) * (2 ^ diff : ℕ)) * 2 ^ d.exponent := by
            simp only [hexact]
      _ = ↑(d.mantissa / (2 ^ diff : ℕ)) * ↑(2 ^ diff : ℕ) * 2 ^ d.exponent := by
            simp only [Int.cast_mul, Int.cast_natCast]
      _ = ↑(d.mantissa / (2 ^ diff : ℕ)) * ((2 : ℚ) ^ diff * 2 ^ d.exponent) := by
            rw [← heq, mul_assoc]
      _ = ↑(d.mantissa / (2 ^ diff : ℕ)) * (2 ^ d.exponent * (2 : ℚ) ^ diff) := by
            rw [mul_comm ((2 : ℚ) ^ diff) (2 ^ d.exponent)]
      _ ≤ ↑(d.mantissa / (2 ^ diff : ℕ)) * (2 ^ d.exponent * (2 : ℚ) ^ diff) := le_refl _

/-! ### Comparison Helper Lemmas -/

/-- Helper: comparing integers reflects comparing rationals when scaled by positive factor -/
private theorem int_lt_iff_rat_mul_lt (a b : ℤ) (c : ℚ) (hc : 0 < c) :
    a < b ↔ (a : ℚ) * c < (b : ℚ) * c :=
    ⟨fun h ↦ mul_lt_mul_of_pos_right (Int.cast_lt.mpr h) hc, fun h ↦ Int.cast_lt.mp
      ((Rat.mul_lt_mul_right hc).mp h)⟩

private theorem int_eq_iff_rat_mul_eq (a b : ℤ) (c : ℚ) (hc : c ≠ 0) :
    a = b ↔ (a : ℚ) * c = (b : ℚ) * c := by
  constructor
  · intro h; rw [h]
  · intro h
    have hcancel := (mul_eq_mul_right_iff (c := c)).mp h
    cases hcancel with
    | inl heq => exact Int.cast_inj.mp heq
    | inr hzero => exact absurd hzero hc

private theorem int_gt_iff_rat_mul_gt (a b : ℤ) (c : ℚ) (hc : 0 < c) :
    a > b ↔ (a : ℚ) * c > (b : ℚ) * c := int_lt_iff_rat_mul_lt b a c hc

/-- Key lemma: shiftLeftInt relates to multiplication by 2^shift in ℚ -/
private theorem shiftLeftInt_toRat (m : ℤ) (n : ℕ) :
    (shiftLeftInt m n : ℚ) = (m : ℚ) * (2 : ℚ) ^ n := by
  simp only [shiftLeftInt, pow2Nat_eq_pow, Int.cast_mul, Int.cast_natCast]
  rw [Nat.cast_pow, Nat.cast_ofNat]

/-- Ord.compare on Int correctly reflects <, =, > -/
private theorem ord_compare_int_lt (a b : ℤ) : Ord.compare a b = .lt ↔ a < b := by
  constructor
  · intro h
    by_contra! hge
    have hcases := lt_or_eq_of_le hge
    cases hcases with
    | inl hgt =>
      simp only [Ord.compare, compareOfLessAndEq, not_lt.mpr (le_of_lt hgt), ne_of_gt hgt,
        ↓reduceIte] at h
      exact absurd h (by decide)
    | inr heq =>
      simp only [Ord.compare, compareOfLessAndEq, heq, lt_irrefl, ↓reduceIte] at h
      exact absurd h (by decide)
  · intro h
    simp only [Ord.compare, compareOfLessAndEq, h, ↓reduceIte]

private theorem ord_compare_int_eq (a b : ℤ) : Ord.compare a b = .eq ↔ a = b := by
  constructor
  · intro h
    by_contra hne
    have hcases := lt_or_gt_of_ne hne
    cases hcases with
    | inl hlt =>
      simp only [Ord.compare, compareOfLessAndEq, hlt, ↓reduceIte] at h
      exact absurd h (by decide)
    | inr hgt =>
      simp only [Ord.compare, compareOfLessAndEq, not_lt.mpr (le_of_lt hgt), ne_of_gt hgt,
        ↓reduceIte] at h
      exact absurd h (by decide)
  · intro h
    simp only [Ord.compare, compareOfLessAndEq, h, lt_irrefl, ↓reduceIte]

private theorem ord_compare_int_gt (a b : ℤ) : Ord.compare a b = .gt ↔ a > b := by
  constructor
  · intro h
    by_contra! hle
    have hcases := lt_or_eq_of_le hle
    cases hcases with
    | inl hlt =>
      simp only [Ord.compare, compareOfLessAndEq, hlt, ↓reduceIte] at h
      exact absurd h (by decide)
    | inr heq =>
      simp only [Ord.compare, compareOfLessAndEq, heq, lt_irrefl, ↓reduceIte] at h
      exact absurd h (by decide)
  · intro h
    simp only [Ord.compare, compareOfLessAndEq, not_lt.mpr (le_of_lt h), ne_of_gt h, ↓reduceIte]

/-- Ord.compare not gt means ≤ -/
private theorem ord_compare_ne_gt_iff (a b : ℤ) : (Ord.compare a b != .gt) = true ↔ a ≤ b := by
  rw [bne_iff_ne, ne_eq]
  constructor
  · intro h
    by_contra! hgt
    have := ord_compare_int_gt a b |>.mpr hgt
    exact h this
  · intro hle hgt
    have := ord_compare_int_gt a b |>.mp hgt
    exact not_lt.mpr hle this

/-! ### Comparison Theorems -/

/-- Helper: Convert aligned integer comparison to toRat comparison (case e₁ ≤ e₂) -/
private theorem aligned_lt_iff_toRat_lt_case1 (d₁ d₂ : Dyadic) (h : d₁.exponent ≤ d₂.exponent) :
    d₁.mantissa < shiftLeftInt d₂.mantissa (d₂.exponent - d₁.exponent).toNat ↔ d₁.toRat < d₂.toRat
      := by
  set shift := (d₂.exponent - d₁.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₂.exponent - d₁.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  -- Key: 2^e₂ = 2^shift * 2^e₁
  have hpow : (2 : ℚ) ^ d₂.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₁.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hpos : (0 : ℚ) < 2 ^ d₁.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
  -- Rewrite RHS: m₂ * 2^e₂ = m₂ * (2^shift * 2^e₁) = (m₂ * 2^shift) * 2^e₁
  have hrhs : (d₂.mantissa : ℚ) * 2 ^ d₂.exponent = d₂.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₁.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hrhs]
  -- Now: m₁ < shiftLeftInt m₂ shift ↔ m₁ * 2^e₁ < (m₂ * 2^shift) * 2^e₁
  rw [int_lt_iff_rat_mul_lt _ _ _ hpos, shiftLeftInt_toRat]

private theorem aligned_eq_iff_toRat_eq_case1 (d₁ d₂ : Dyadic) (h : d₁.exponent ≤ d₂.exponent) :
    d₁.mantissa = shiftLeftInt d₂.mantissa (d₂.exponent - d₁.exponent).toNat ↔ d₁.toRat = d₂.toRat
      := by
  set shift := (d₂.exponent - d₁.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₂.exponent - d₁.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  have hpow : (2 : ℚ) ^ d₂.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₁.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hne : (2 : ℚ) ^ d₁.exponent ≠ 0 := zpow_ne_zero _ (two_ne_zero)
  have hrhs : (d₂.mantissa : ℚ) * 2 ^ d₂.exponent = d₂.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₁.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hrhs, int_eq_iff_rat_mul_eq _ _ _ hne, shiftLeftInt_toRat]

private theorem aligned_gt_iff_toRat_gt_case1 (d₁ d₂ : Dyadic) (h : d₁.exponent ≤ d₂.exponent) :
    d₁.mantissa > shiftLeftInt d₂.mantissa (d₂.exponent - d₁.exponent).toNat ↔ d₁.toRat > d₂.toRat
      := by
  set shift := (d₂.exponent - d₁.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₂.exponent - d₁.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  have hpow : (2 : ℚ) ^ d₂.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₁.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hpos : (0 : ℚ) < 2 ^ d₁.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
  have hrhs : (d₂.mantissa : ℚ) * 2 ^ d₂.exponent = d₂.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₁.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hrhs, int_gt_iff_rat_mul_gt _ _ _ hpos, shiftLeftInt_toRat]

/-- Helper: Convert aligned integer comparison to toRat comparison (case e₁ > e₂) -/
private theorem aligned_lt_iff_toRat_lt_case2 (d₁ d₂ : Dyadic) (h : d₁.exponent > d₂.exponent) :
    shiftLeftInt d₁.mantissa (d₁.exponent - d₂.exponent).toNat < d₂.mantissa ↔ d₁.toRat < d₂.toRat
      := by
  set shift := (d₁.exponent - d₂.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₁.exponent - d₂.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  have hpow : (2 : ℚ) ^ d₁.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₂.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hpos : (0 : ℚ) < 2 ^ d₂.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
  -- Rewrite LHS: m₁ * 2^e₁ = m₁ * (2^shift * 2^e₂) = (m₁ * 2^shift) * 2^e₂
  have hlhs : (d₁.mantissa : ℚ) * 2 ^ d₁.exponent = d₁.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₂.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hlhs, int_lt_iff_rat_mul_lt _ _ _ hpos, shiftLeftInt_toRat]

private theorem aligned_eq_iff_toRat_eq_case2 (d₁ d₂ : Dyadic) (h : d₁.exponent > d₂.exponent) :
    shiftLeftInt d₁.mantissa (d₁.exponent - d₂.exponent).toNat = d₂.mantissa ↔ d₁.toRat = d₂.toRat
      := by
  set shift := (d₁.exponent - d₂.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₁.exponent - d₂.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  have hpow : (2 : ℚ) ^ d₁.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₂.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hne : (2 : ℚ) ^ d₂.exponent ≠ 0 := zpow_ne_zero _ (two_ne_zero)
  have hlhs : (d₁.mantissa : ℚ) * 2 ^ d₁.exponent = d₁.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₂.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hlhs, int_eq_iff_rat_mul_eq _ _ _ hne, shiftLeftInt_toRat]

private theorem aligned_gt_iff_toRat_gt_case2 (d₁ d₂ : Dyadic) (h : d₁.exponent > d₂.exponent) :
    shiftLeftInt d₁.mantissa (d₁.exponent - d₂.exponent).toNat > d₂.mantissa ↔ d₁.toRat > d₂.toRat
      := by
  set shift := (d₁.exponent - d₂.exponent).toNat with hshift_def
  have hshift : (shift : ℤ) = d₁.exponent - d₂.exponent := by
    rw [hshift_def, Int.toNat_of_nonneg]; omega
  rw [toRat_eq, toRat_eq]
  have hpow : (2 : ℚ) ^ d₁.exponent = (2 : ℚ) ^ (shift : ℤ) * 2 ^ d₂.exponent := by
    rw [← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), hshift]; congr 1; omega
  have hpos : (0 : ℚ) < 2 ^ d₂.exponent := zpow_pos (by norm_num : (0 : ℚ) < 2) _
  have hlhs : (d₁.mantissa : ℚ) * 2 ^ d₁.exponent = d₁.mantissa * (2 : ℚ) ^ shift * 2 ^
    d₂.exponent := by
    rw [hpow, zpow_natCast, mul_assoc]
  rw [hlhs, int_gt_iff_rat_mul_gt _ _ _ hpos, shiftLeftInt_toRat]

/-- le is correct with respect to toRat ordering -/
theorem le_iff_toRat_le (d₁ d₂ : Dyadic) :
    le d₁ d₂ = true ↔ d₁.toRat ≤ d₂.toRat := by
  unfold le compare
  split_ifs with h
  · -- Case: d₁.exponent ≤ d₂.exponent
    set shift := (d₂.exponent - d₁.exponent).toNat
    rw [ord_compare_ne_gt_iff]
    constructor
    · intro hle
      by_cases! hlt : d₁.mantissa < shiftLeftInt d₂.mantissa shift
      · exact le_of_lt ((aligned_lt_iff_toRat_lt_case1 d₁ d₂ h).mp hlt)
      · have heq_or_gt := lt_or_eq_of_le hlt
        cases heq_or_gt with
        | inl hgt =>
          exfalso; exact not_lt.mpr hle hgt
        | inr heq =>
          exact le_of_eq ((aligned_eq_iff_toRat_eq_case1 d₁ d₂ h).mp heq.symm)
    · intro hle
      by_contra! hgt
      have hgt' := (aligned_gt_iff_toRat_gt_case1 d₁ d₂ h).mp hgt
      exact not_lt.mpr hle hgt'
  · -- Case: d₁.exponent > d₂.exponent
    push Not at h
    set shift := (d₁.exponent - d₂.exponent).toNat
    rw [ord_compare_ne_gt_iff]
    constructor
    · intro hle
      by_cases! hlt : shiftLeftInt d₁.mantissa shift < d₂.mantissa
      · exact le_of_lt ((aligned_lt_iff_toRat_lt_case2 d₁ d₂ h).mp hlt)
      · have heq_or_gt := lt_or_eq_of_le hlt
        cases heq_or_gt with
        | inl hgt =>
          exfalso; exact not_lt.mpr hle hgt
        | inr heq =>
          exact le_of_eq ((aligned_eq_iff_toRat_eq_case2 d₁ d₂ h).mp heq.symm)
    · intro hle
      by_contra! hgt
      have hgt' := (aligned_gt_iff_toRat_gt_case2 d₁ d₂ h).mp hgt
      exact not_lt.mpr hle hgt'

/-- compare reflects toRat ordering: lt case -/
theorem compare_lt_iff (d₁ d₂ : Dyadic) :
    compare d₁ d₂ = .lt ↔ d₁.toRat < d₂.toRat := by
  unfold compare
  split_ifs with h
  · rw [ord_compare_int_lt]; exact aligned_lt_iff_toRat_lt_case1 d₁ d₂ h
  · push Not at h; rw [ord_compare_int_lt]; exact aligned_lt_iff_toRat_lt_case2 d₁ d₂ h

/-- compare reflects toRat ordering: gt case -/
theorem compare_gt_iff (d₁ d₂ : Dyadic) :
    compare d₁ d₂ = .gt ↔ d₁.toRat > d₂.toRat := by
  unfold compare
  split_ifs with h
  · rw [ord_compare_int_gt]; exact aligned_gt_iff_toRat_gt_case1 d₁ d₂ h
  · push Not at h; rw [ord_compare_int_gt]; exact aligned_gt_iff_toRat_gt_case2 d₁ d₂ h

/-- compare reflects toRat ordering: eq case -/
theorem compare_eq_iff (d₁ d₂ : Dyadic) :
    compare d₁ d₂ = .eq ↔ d₁.toRat = d₂.toRat := by
  unfold compare
  split_ifs with h
  · rw [ord_compare_int_eq]; exact aligned_eq_iff_toRat_eq_case1 d₁ d₂ h
  · push Not at h; rw [ord_compare_int_eq]; exact aligned_eq_iff_toRat_eq_case2 d₁ d₂ h

/-! ### Min/Max Lemmas -/

/-- min produces value ≤ first argument -/
theorem min_toRat_le_left (d₁ d₂ : Dyadic) : (min d₁ d₂).toRat ≤ d₁.toRat := by
  unfold min
  split_ifs with h
  · exact le_refl _
  · exact le_of_not_ge (fun hle => h (le_iff_toRat_le d₁ d₂ |>.mpr hle))

/-- min produces value ≤ second argument -/
theorem min_toRat_le_right (d₁ d₂ : Dyadic) : (min d₁ d₂).toRat ≤ d₂.toRat := by
  unfold min
  split_ifs with h
  · exact le_iff_toRat_le d₁ d₂ |>.mp h
  · exact le_refl _

/-- first argument ≤ max -/
theorem le_max_toRat_left (d₁ d₂ : Dyadic) : d₁.toRat ≤ (max d₁ d₂).toRat := by
  unfold max
  split_ifs with h
  · exact le_iff_toRat_le d₁ d₂ |>.mp h
  · exact le_refl _

/-- second argument ≤ max -/
theorem le_max_toRat_right (d₁ d₂ : Dyadic) : d₂.toRat ≤ (max d₁ d₂).toRat := by
  unfold max
  split_ifs with h
  · exact le_refl _
  · exact le_of_not_ge (fun hle => h (le_iff_toRat_le d₁ d₂ |>.mpr hle))

/-- Dyadic.min commutes with toRat -/
theorem min_toRat (d₁ d₂ : Dyadic) : (min d₁ d₂).toRat = Min.min d₁.toRat d₂.toRat := by
  unfold min
  split_ifs with h
  · -- h : le d₁ d₂
    have hle : d₁.toRat ≤ d₂.toRat := le_iff_toRat_le d₁ d₂ |>.mp h
    exact (min_eq_left hle).symm
  · -- ¬ le d₁ d₂, so d₂.toRat < d₁.toRat
    have hgt : d₂.toRat < d₁.toRat := by
      have := le_iff_toRat_le d₁ d₂
      exact lt_of_not_ge (fun hle => h (this.mpr hle))
    exact (min_eq_right (le_of_lt hgt)).symm

/-- Dyadic.max commutes with toRat -/
theorem max_toRat (d₁ d₂ : Dyadic) : (max d₁ d₂).toRat = Max.max d₁.toRat d₂.toRat := by
  unfold max
  split_ifs with h
  · -- h : le d₁ d₂
    have hle : d₁.toRat ≤ d₂.toRat := le_iff_toRat_le d₁ d₂ |>.mp h
    exact (max_eq_right hle).symm
  · -- ¬ le d₁ d₂, so d₂.toRat < d₁.toRat
    have hgt : d₂.toRat < d₁.toRat := by
      have := le_iff_toRat_le d₁ d₂
      exact lt_of_not_ge (fun hle => h (this.mpr hle))
    exact (max_eq_left (le_of_lt hgt)).symm

/-- min4 ≤ max4 -/
theorem min4_le_max4 (a b c d : Dyadic) : (min4 a b c d).toRat ≤ (max4 a b c d).toRat := by
  unfold min4 max4
  calc (min (min a b) (min c d)).toRat
      ≤ (min a b).toRat := min_toRat_le_left _ _
    _ ≤ a.toRat := min_toRat_le_left _ _
    _ ≤ (max a b).toRat := le_max_toRat_left _ _
    _ ≤ (max (max a b) (max c d)).toRat := le_max_toRat_left _ _

/-! ### Normalize Lemmas -/

/-- normalizeDown produces value ≤ original -/
theorem toRat_normalizeDown_le (d : Dyadic) (maxBits : Nat) :
    (d.normalizeDown maxBits).toRat ≤ d.toRat := by
  unfold normalizeDown normalize
  simp only [Bool.false_eq_true, ↓reduceIte]
  split_ifs with h
  · exact le_refl _
  · exact toRat_shiftDown_le d _

/-- normalizeUp produces value ≥ original -/
theorem toRat_normalizeUp_ge (d : Dyadic) (maxBits : Nat) :
    d.toRat ≤ (d.normalizeUp maxBits).toRat := by
  unfold normalizeUp normalize
  simp only [↓reduceIte]
  split_ifs with h
  · exact le_refl _
  · exact toRat_shiftUp_ge d _

/-! ### Scale2 Lemmas -/

/-- scale2 multiplies by 2^n -/
theorem toRat_scale2 (d : Dyadic) (n : Int) :
    (d.scale2 n).toRat = d.toRat * (2 : ℚ) ^ n := by
  unfold scale2
  rw [toRat_eq, toRat_eq]
  simp only []
  rw [mul_assoc, ← zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0)]

/-- scale2 preserves order -/
theorem toRat_scale2_le_scale2 (d₁ d₂ : Dyadic) (n : Int) (h : d₁.toRat ≤ d₂.toRat) :
    (d₁.scale2 n).toRat ≤ (d₂.scale2 n).toRat := by
  rw [toRat_scale2, toRat_scale2]
  exact mul_le_mul_of_nonneg_right h (zpow_nonneg (by norm_num : (0 : ℚ) ≤ 2) n)

/-! ### Square Root Operations -/

/-- Integer square root of a natural number.
    Satisfies: `(intSqrtNat n)^2 ≤ n < (intSqrtNat n + 1)^2` -/
def intSqrtNat (n : Nat) : Nat := Nat.sqrt n

/-- Integer square root of a non-negative integer.
    Returns 0 for negative inputs. -/
def intSqrt (n : Int) : Int :=
  if n < 0 then 0 else Int.ofNat (intSqrtNat n.toNat)

/-- Key property of Nat.sqrt: `Nat.sqrt n ^ 2 ≤ n` -/
private theorem nat_sqrt_sq_le (n : Nat) : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n

/-- Key property of Nat.sqrt: `n < (Nat.sqrt n + 1) ^ 2` -/
private theorem nat_lt_succ_sqrt_sq (n : Nat) : n < (Nat.sqrt n + 1) ^ 2 := by
  have h := Nat.lt_succ_sqrt n
  simp only [Nat.succ_eq_add_one] at h
  rw [sq]
  exact h

/-- intSqrt n ^ 2 ≤ n for n ≥ 0 -/
theorem intSqrt_sq_le {n : Int} (hn : 0 ≤ n) : (intSqrt n) ^ 2 ≤ n := by
  simp only [intSqrt, not_lt.mpr hn, ↓reduceIte, intSqrtNat]
  have h := nat_sqrt_sq_le n.toNat
  calc ((Nat.sqrt n.toNat : ℤ) ^ 2 : ℤ)
      = ((Nat.sqrt n.toNat) ^ 2 : ℕ) := by norm_cast
    _ ≤ (n.toNat : ℤ) := Int.ofNat_le.mpr h
    _ = n := Int.toNat_of_nonneg hn

/-- n < (intSqrt n + 1) ^ 2 for n ≥ 0 -/
theorem int_lt_succ_sqrt_sq {n : Int} (hn : 0 ≤ n) : n < (intSqrt n + 1) ^ 2 := by
  simp only [intSqrt, not_lt.mpr hn, ↓reduceIte, intSqrtNat]
  have h := nat_lt_succ_sqrt_sq n.toNat
  calc n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn).symm
    _ < ((Nat.sqrt n.toNat + 1) ^ 2 : ℕ) := Int.ofNat_lt.mpr h
    _ = ((Nat.sqrt n.toNat : ℤ) + 1) ^ 2 := by norm_cast

/-- intSqrt is nonnegative for nonnegative inputs -/
theorem intSqrt_nonneg {n : Int} (hn : 0 ≤ n) : 0 ≤ intSqrt n := by
  simp only [intSqrt, not_lt.mpr hn, ↓reduceIte, intSqrtNat]
  exact Int.natCast_nonneg _

/-- Compute sqrt(d) with a target exponent `prec`.
    Returns a Dyadic with exponent `prec` such that result ≤ sqrt(d).

    For d = m * 2^e, we compute:
    - shift = e - 2*prec (to align for sqrt)
    - m' = m * 2^shift (or m / 2^(-shift) if shift < 0)
    - result = floor(sqrt(m')) * 2^prec

    This ensures: result.toRat ≤ sqrt(d.toRat) -/
def sqrtDown (d : Dyadic) (prec : Int) : Dyadic :=
  if d.mantissa < 0 then zero
  else
    let shift := d.exponent - 2 * prec
    let m := if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int)
    ⟨intSqrt m, prec⟩

/-- Compute sqrt(d) rounded up with target exponent `prec`.
    Returns a Dyadic with exponent `prec` such that result ≥ sqrt(d).

    Uses the same computation as sqrtDown, but if the result is not
    a perfect square, adds 1 to round up. -/
def sqrtUp (d : Dyadic) (prec : Int) : Dyadic :=
  if d.mantissa < 0 then zero
  else
    let shift := d.exponent - 2 * prec
    let m := if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int)
    let s := intSqrt m
    -- If m is a perfect square of s, return s; otherwise s+1
    if s * s = m then ⟨s, prec⟩ else ⟨s + 1, prec⟩

/-! #### Sqrt Correctness Theorems -/

/-- Helper: For non-negative m and shift ≥ 0, the scaled mantissa is non-negative -/
private theorem sqrt_scaled_shift_nonneg {m : Int} {shift : Int}
    (hm : 0 ≤ m) (_hshift : 0 ≤ shift) :
    0 ≤ m * (pow2Nat shift.toNat : Int) := by
  apply mul_nonneg hm
  exact Int.natCast_nonneg _

/-- sqrtDown is non-negative for non-negative inputs -/
theorem sqrtDown_nonneg (d : Dyadic) (prec : Int) (hd : 0 ≤ d.mantissa) :
    0 ≤ (sqrtDown d prec).mantissa := by
  simp only [sqrtDown, not_lt.mpr hd, ↓reduceIte]
  set shift := d.exponent - 2 * prec
  have hm_nonneg : 0 ≤ (if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int)) := by
    by_cases! hsh : shift ≥ 0
    · simp only [hsh, ↓reduceIte]
      exact sqrt_scaled_shift_nonneg hd hsh
    · simp only [not_le.mpr hsh, ↓reduceIte]
      exact Int.ediv_nonneg hd (Int.natCast_nonneg _)
  exact intSqrt_nonneg hm_nonneg

/-- sqrtUp is non-negative for non-negative inputs -/
theorem sqrtUp_nonneg (d : Dyadic) (prec : Int) (hd : 0 ≤ d.mantissa) :
    0 ≤ (sqrtUp d prec).mantissa := by
  simp only [sqrtUp, not_lt.mpr hd, ↓reduceIte]
  set shift := d.exponent - 2 * prec
  have hm_nonneg : 0 ≤ (if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int)) := by
    by_cases! hsh : shift ≥ 0
    · simp only [hsh, ↓reduceIte]
      exact sqrt_scaled_shift_nonneg hd hsh
    · simp only [not_le.mpr hsh, ↓reduceIte]
      exact Int.ediv_nonneg hd (Int.natCast_nonneg _)
  set m := (if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int))
  set s := intSqrt m
  by_cases hperfect : s * s = m
  · simp only [hperfect, ↓reduceIte]
    exact intSqrt_nonneg hm_nonneg
  · simp only [hperfect, ↓reduceIte]
    calc 0 ≤ s := intSqrt_nonneg hm_nonneg
      _ ≤ s + 1 := by omega

/-- sqrtDown.toRat ≤ sqrtUp.toRat for non-negative inputs -/
theorem sqrtDown_le_sqrtUp (d : Dyadic) (prec : Int) (hd : 0 ≤ d.mantissa) :
    (sqrtDown d prec).toRat ≤ (sqrtUp d prec).toRat := by
  simp only [sqrtDown, sqrtUp, not_lt.mpr hd, ↓reduceIte]
  set shift := d.exponent - 2 * prec
  have hm_nonneg : 0 ≤ (if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int)) := by
    by_cases! hsh : shift ≥ 0
    · simp only [hsh, ↓reduceIte]
      exact sqrt_scaled_shift_nonneg hd hsh
    · simp only [not_le.mpr hsh, ↓reduceIte]
      exact Int.ediv_nonneg hd (Int.natCast_nonneg _)
  set m := (if shift ≥ 0 then
      d.mantissa * (pow2Nat shift.toNat : Int)
    else
      d.mantissa / (pow2Nat (-shift).toNat : Int))
  set s := intSqrt m
  by_cases hperfect : s * s = m
  · -- Perfect square: both return s
    simp only [hperfect, ↓reduceIte]
    exact le_refl _
  · -- Non-perfect: sqrtDown returns s, sqrtUp returns s+1
    simp only [hperfect, ↓reduceIte]
    rw [toRat_eq, toRat_eq]
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos (by norm_num : (0 : ℚ) < 2) _))
    simp only [Int.cast_add, Int.cast_one]
    exact le_add_of_nonneg_right (by norm_num : (0 : ℚ) ≤ 1)

end Dyadic
end LeanCert.Core
