/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Rat.Floor
public import LeanPool.Ratpoints.Model.Double
public import LeanPool.Ratpoints.Spec.Region

import Mathlib.Algebra.Order.Floor.Semifield
import LeanPool.Ratpoints.Mathlib.Algebra.Order.Field.Basic
import LeanPool.Ratpoints.Mathlib.Order.WithBotTop

/-!
# Values and order of binary64 interval endpoints

The interval specification assigns finite doubles their exact rational values and recognizes both
infinities. The comparisons follow this order off NaN. The integer conversion and power-of-two
scaling lemmas justify exact endpoint computations within the ranges used by the Sturm step.
-/

@[expose] public section

namespace Ratpoints

namespace Double

theorem doubleValue_huge : doubleValue huge.bits = ⊤ := by decide

theorem doubleValue_huge_neg : doubleValue huge.neg.bits = ⊥ := by decide

theorem expField_eq (x : Double) : x.expField = x.bits.toNat / 2 ^ 52 % 2 ^ 11 := by
  rw [expField, UInt64.toNat_and, UInt64.toNat_shiftRight,
    show (0x7ff : UInt64).toNat = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  rfl

theorem fracField_eq (x : Double) : x.fracField = x.bits.toNat % 2 ^ 52 := by
  rw [fracField, UInt64.toNat_and, show (0xfffffffffffff : UInt64).toNat = 2 ^ 52 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_and_mask (b : UInt64) : (b &&& 0x7fffffffffffffff).toNat = b.toNat % 2 ^ 63 := by
  rw [UInt64.toNat_and, show (0x7fffffffffffffff : UInt64).toNat = 2 ^ 63 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem signBit_eq_decide (x : Double) : x.signBit = decide (2 ^ 63 ≤ x.bits.toNat) := by
  simp only [signBit]
  exact decide_eq_decide.mpr (by lia [x.bits.toNat_lt])

theorem signBit_eq_true_iff (x : Double) : x.signBit = true ↔ 2 ^ 63 ≤ x.bits.toNat := by
  simp [signBit_eq_decide]

theorem fracField_lt (x : Double) : x.fracField < 2 ^ 52 :=
  fracField_eq x ▸ Nat.mod_lt _ (Nat.two_pow_pos 52)

theorem expField_lt (x : Double) : x.expField < 2048 :=
  expField_eq x ▸ Nat.mod_lt _ (Nat.two_pow_pos 11)

theorem toNat_bits (x : Double) :
    x.bits.toNat = (if x.signBit then 2 ^ 63 else 0) + (x.expField * 2 ^ 52 + x.fracField) := by
  have h := x.bits.toNat_lt
  have h1 := Nat.div_add_mod x.bits.toNat (2 ^ 52)
  have h2 := Nat.div_add_mod (x.bits.toNat / 2 ^ 52) (2 ^ 11)
  rw [signBit_eq_decide, expField_eq, fracField_eq]
  split <;> rename_i h3 <;> simp only [decide_eq_true_eq] at h3 <;> lia

theorem expField_mul_add_fracField (x : Double) :
    x.expField * 2 ^ 52 + x.fracField = x.bits.toNat % 2 ^ 63 := by
  rw [toNat_bits x]; split <;> lia [fracField_lt x, expField_lt x]

theorem isNaN_iff (x : Double) : x.isNaN = true ↔ IsNaN x.bits := by
  simp [isNaN, IsNaN, expField_eq, fracField_eq]

theorem fields_eq_of_toNat_bits_eq {x : Double} {neg : Bool} {E F : ℕ} (hE : E < 2048)
    (hF : F < 2 ^ 52) (h : x.bits.toNat = (if neg then 2 ^ 63 else 0) + (E * 2 ^ 52 + F)) :
    x.signBit = neg ∧ x.expField = E ∧ x.fracField = F := by
  have e : F + 2 ^ 52 * ((if neg then 2 ^ 11 else 0) + E) = x.bits.toNat := by
    rw [h]; cases neg <;> simp <;> lia
  have hd := (Nat.div_mod_unique (Nat.two_pow_pos 52)).mpr ⟨e, hF⟩
  rw [signBit_eq_decide, expField_eq, fracField_eq, hd.1, hd.2, Nat.add_mod,
    Nat.mod_eq_of_lt (show E < 2 ^ 11 by lia)]
  cases neg <;> simp [h] <;> lia

/-! ### The exact value of a finite double -/

theorem toRat_eq (x : Double) : x.toRat = (x.toDyadic.1 : ℚ) * 2 ^ x.toDyadic.2 := by
  rcases h : x.toDyadic with ⟨m, e⟩
  simp only [toRat, h]
  split_ifs with he
  · push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg he]
  · rw [Rat.mkRat_eq_div]
    push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by lia), zpow_neg, div_inv_eq_mul]

theorem toDyadic_eq (x : Double) : x.toDyadic =
    ((if x.signBit then -1 else 1 : ℤ) *
      ((if x.expField = 0 then x.fracField else x.fracField + 2 ^ 52 : ℕ) : ℤ),
      if x.expField = 0 then -1074 else (x.expField : ℤ) - 1075) := by
  simp only [toDyadic]
  split_ifs <;> simp

theorem toRat_eq_fields (x : Double) : x.toRat = (if x.signBit then -1 else 1) *
    (if x.expField = 0 then (x.fracField : ℚ) * 2 ^ (-1074 : ℤ)
      else (2 ^ 52 + x.fracField) * 2 ^ ((x.expField : ℤ) - 1075)) := by
  rw [toRat_eq, toDyadic_eq]
  split_ifs <;> simp only [Int.cast_mul, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Int.cast_add, Int.cast_pow, Int.cast_ofNat,
    mul_assoc, add_comm]

/-- The value that the specification gives the bits of a double (`Ratpoints.doubleValue`), by the
fields of the model: `±∞` for the exponent field `2047` and the exact value
`Ratpoints.Double.toRat` otherwise. -/
theorem doubleValue_bits (x : Double) : doubleValue x.bits =
    if x.expField = 2047 then (if x.signBit then ⊥ else ⊤) else (x.toRat : WithBotTop ℚ) := by
  simp only [doubleValue, ← expField_eq, ← fracField_eq, ← signBit_eq_true_iff, toRat_eq_fields]
  split_ifs <;> simp

theorem doubleValue_eq_toRat {x : Double} (hx : x.isFinite = true) :
    doubleValue x.bits = (x.toRat : WithBotTop ℚ) := by
  rw [doubleValue_bits, ite_eq_right (by simpa [isFinite] using hx)]

/-- The value of a finite double `x` with `Ratpoints.Double.toDyadic x = (m, e)` as the fraction of
`m 2 ^ max e 0` and `2 ^ max (-e) 0`. -/
theorem doubleValue_eq_of_toDyadic_eq {x : Double} (hf : x.isFinite = true) {m e : ℤ}
    (hd : x.toDyadic = (m, e)) :
    doubleValue x.bits = ((((m * 2 ^ e.toNat : ℤ) : ℚ) / ((2 ^ (-e).toNat : ℕ) : ℚ) : ℚ) :
      WithBotTop ℚ) := by
  rw [doubleValue_eq_toRat hf, intCast_mul_two_pow_div_two_pow, toRat_eq, hd]

/-! ### The order of the values -/

/-- The order value (`Ratpoints.Double.orderValue`) of `+∞`, `2047 · 2 ^ 52`, the bits of `+∞`;
`-maxOrderValue` is that of `-∞`. -/
def maxOrderValue : ℕ := 2047 * 2 ^ 52

/-- The value of the nonnegative finite double with the bits `a`, in units of the least subnormal
`2 ^ (-1074)`: the fraction `f` for the exponent field `0`, and `(2 ^ 52 + f) 2 ^ (e - 1)` for an
exponent field `e ≥ 1`. -/
def magnitudeUnits (a : ℕ) : ℕ :=
  if a / 2 ^ 52 = 0 then a % 2 ^ 52 else (2 ^ 52 + a % 2 ^ 52) * 2 ^ (a / 2 ^ 52 - 1)

/-- `Ratpoints.Double.magnitudeUnits` with the sign of the order value `k`, the value of the finite
doubles with the order value `k` in units of `2 ^ (-1074)`. -/
def orderValueUnits (k : ℤ) : ℤ :=
  if k < 0 then -(magnitudeUnits k.natAbs : ℤ) else magnitudeUnits k.natAbs

/-- The value of the doubles with the order value `k` (`Ratpoints.Double.orderValue`), for
`|k| ≤ Ratpoints.Double.maxOrderValue`: `⊥` at `-maxOrderValue`, `⊤` at `maxOrderValue`, and
`Ratpoints.Double.orderValueUnits k` times `2 ^ (-1074)` between. -/
def valueOfOrderValue (k : ℤ) : WithBotTop ℚ :=
  if k ≤ -(maxOrderValue : ℤ) then ⊥ else if (maxOrderValue : ℤ) ≤ k then ⊤
  else (((orderValueUnits k : ℚ) * 2 ^ (-1074 : ℤ) : ℚ) : WithBotTop ℚ)

theorem magnitudeUnits_lt_two_pow (a : ℕ) : magnitudeUnits a < 2 ^ (52 + a / 2 ^ 52) := by
  simp only [magnitudeUnits]
  split_ifs with h
  · rw [h]; exact Nat.mod_lt _ (Nat.two_pow_pos 52)
  · have := Nat.mod_lt a (Nat.two_pow_pos 52)
    calc (2 ^ 52 + a % 2 ^ 52) * 2 ^ (a / 2 ^ 52 - 1) < 2 ^ 53 * 2 ^ (a / 2 ^ 52 - 1) :=
          Nat.mul_lt_mul_of_pos_right (by lia) (Nat.two_pow_pos _)
      _ = 2 ^ (52 + a / 2 ^ 52) := by rw [← Nat.pow_add]; congr 1; lia

theorem two_pow_le_magnitudeUnits {a : ℕ} (h : a / 2 ^ 52 ≠ 0) :
    2 ^ (51 + a / 2 ^ 52) ≤ magnitudeUnits a := by
  simp only [magnitudeUnits, h, ↓reduceIte]
  rw [show 51 + a / 2 ^ 52 = 52 + (a / 2 ^ 52 - 1) by lia, Nat.pow_add]
  exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

theorem magnitudeUnits_strictMono : StrictMono magnitudeUnits := by
  intro a b hab
  rcases (Nat.div_le_div_right (c := 2 ^ 52) hab.le).lt_or_eq with h | h
  · calc magnitudeUnits a < 2 ^ (52 + a / 2 ^ 52) := magnitudeUnits_lt_two_pow a
      _ ≤ 2 ^ (51 + b / 2 ^ 52) := Nat.pow_le_pow_right (by decide) (by lia)
      _ ≤ magnitudeUnits b := two_pow_le_magnitudeUnits (by lia)
  · have h1 := Nat.div_add_mod a (2 ^ 52)
    have h2 := Nat.div_add_mod b (2 ^ 52)
    have hf : a % 2 ^ 52 < b % 2 ^ 52 := by rw [h] at h1; lia
    simp only [magnitudeUnits]
    rw [h]
    split_ifs
    · exact hf
    · exact Nat.mul_lt_mul_of_pos_right (by lia) (Nat.two_pow_pos _)

@[simp]
theorem magnitudeUnits_zero : magnitudeUnits 0 = 0 := rfl

theorem orderValueUnits_strictMono : StrictMono orderValueUnits := by
  intro k l hkl
  have hm := magnitudeUnits_strictMono
  have h0 (n : ℕ) (hn : 0 < n) : 0 < magnitudeUnits n := magnitudeUnits_zero ▸ hm hn
  simp only [orderValueUnits]
  split_ifs with h1 h2 h2
  · lia [hm (show l.natAbs < k.natAbs by lia)]
  · lia [h0 k.natAbs (by lia)]
  · lia
  · lia [hm (show k.natAbs < l.natAbs by lia)]

theorem strictMonoOn_valueOfOrderValue :
    StrictMonoOn valueOfOrderValue (Set.Icc (-(maxOrderValue : ℤ)) maxOrderValue) := by
  intro k ⟨hk1, hk2⟩ l ⟨hl1, hl2⟩ hkl
  have hs : (orderValueUnits k : ℚ) < orderValueUnits l := mod_cast orderValueUnits_strictMono hkl
  simp only [valueOfOrderValue]
  split_ifs <;> try lia
  all_goals first
    | exact WithBotTop.bot_lt_coe _
    | exact WithBotTop.coe_lt_top _
    | exact bot_lt_top
    | exact WithBotTop.coe_lt_coe.mpr (mul_lt_mul_of_pos_right hs (zpow_pos two_pos _))

theorem orderValue_eq_mod (x : Double) : x.orderValue = if x.signBit
    then -((x.bits.toNat % 2 ^ 63 : ℕ) : ℤ) else ((x.bits.toNat % 2 ^ 63 : ℕ) : ℤ) := by
  simp only [orderValue, toNat_and_mask]

theorem orderValue_eq (x : Double) : x.orderValue =
    if x.signBit then -((x.expField * 2 ^ 52 + x.fracField : ℕ) : ℤ)
    else ((x.expField * 2 ^ 52 + x.fracField : ℕ) : ℤ) := by
  rw [orderValue_eq_mod, expField_mul_add_fracField]

theorem expField_lt_or_of_isNaN_eq_false {x : Double} (hx : x.isNaN = false) :
    x.expField < 2047 ∨ x.expField = 2047 ∧ x.fracField = 0 := by
  simp only [isNaN, Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hx
  lia [expField_lt x]

theorem natAbs_orderValue_le {x : Double} (hx : x.isNaN = false) :
    x.orderValue.natAbs ≤ maxOrderValue := by
  rw [orderValue_eq, maxOrderValue]
  rcases expField_lt_or_of_isNaN_eq_false hx with h | h <;> split <;> lia [fracField_lt x]

theorem orderValue_mem_Icc {x : Double} (hx : x.isNaN = false) :
    x.orderValue ∈ Set.Icc (-(maxOrderValue : ℤ)) maxOrderValue := by
  constructor <;> lia [natAbs_orderValue_le hx]

theorem magnitudeUnits_fields {E F : ℕ} (hF : F < 2 ^ 52) :
    magnitudeUnits (E * 2 ^ 52 + F) = if E = 0 then F else (2 ^ 52 + F) * 2 ^ (E - 1) := by
  have hd := (Nat.div_mod_unique (Nat.two_pow_pos 52)).mpr
    ⟨show F + 2 ^ 52 * E = E * 2 ^ 52 + F by lia, hF⟩
  rw [magnitudeUnits, hd.1, hd.2]

theorem orderValueUnits_natCast (n : ℕ) : orderValueUnits n = magnitudeUnits n := by
  simp [orderValueUnits]

theorem orderValueUnits_neg_natCast (n : ℕ) :
    orderValueUnits (-(n : ℤ)) = -(magnitudeUnits n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [orderValueUnits]
  · simp [orderValueUnits, h]

theorem magnitudeUnits_mul_eq {E F : ℕ} (hF : F < 2 ^ 52) :
    (magnitudeUnits (E * 2 ^ 52 + F) : ℚ) * 2 ^ (-1074 : ℤ) =
      if E = 0 then (F : ℚ) * 2 ^ (-1074 : ℤ) else (2 ^ 52 + F) * 2 ^ ((E : ℤ) - 1075) := by
  rw [magnitudeUnits_fields hF]
  split_ifs with h
  · rfl
  · rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc, ← zpow_natCast,
      ← zpow_add₀ two_ne_zero, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h)]
    push_cast
    congr 2
    lia

theorem valueOfOrderValue_natCast {k : ℕ} (hk : k < maxOrderValue) :
    valueOfOrderValue k = (((magnitudeUnits k : ℚ) * 2 ^ (-1074 : ℤ) : ℚ) : WithBotTop ℚ) := by
  have h1 : ¬((k : ℤ) ≤ -(maxOrderValue : ℤ)) := by lia
  have h2 : ¬((maxOrderValue : ℤ) ≤ k) := by lia
  simp only [valueOfOrderValue, h1, h2, ↓reduceIte, orderValueUnits_natCast, Int.cast_natCast]

theorem valueOfOrderValue_neg_natCast {k : ℕ} (hk : k < maxOrderValue) :
    valueOfOrderValue (-(k : ℤ)) =
      ((-((magnitudeUnits k : ℚ) * 2 ^ (-1074 : ℤ)) : ℚ) : WithBotTop ℚ) := by
  have h1 : ¬(-(k : ℤ) ≤ -(maxOrderValue : ℤ)) := by lia
  have h2 : ¬((maxOrderValue : ℤ) ≤ -(k : ℤ)) := by lia
  simp only [valueOfOrderValue, h1, h2, ↓reduceIte, orderValueUnits_neg_natCast, Int.cast_neg,
    Int.cast_natCast, neg_mul]

theorem doubleValue_eq_valueOfOrderValue {x : Double} (hx : x.isNaN = false) :
    doubleValue x.bits = valueOfOrderValue x.orderValue := by
  rw [doubleValue_bits, orderValue_eq]
  rcases expField_lt_or_of_isNaN_eq_false hx with h | ⟨h, h0⟩
  · have hk : x.expField * 2 ^ 52 + x.fracField < maxOrderValue := by
      rw [maxOrderValue]; lia [fracField_lt x]
    rw [ite_eq_right h.ne, toRat_eq_fields, ← magnitudeUnits_mul_eq (fracField_lt x)]
    cases x.signBit <;> simp only [Bool.false_eq_true, ↓reduceIte, valueOfOrderValue_natCast hk,
      valueOfOrderValue_neg_natCast hk, one_mul, neg_one_mul]
  · cases x.signBit <;> simp [h, h0, valueOfOrderValue, maxOrderValue]

theorem lt_eq_true_iff {x y : Double} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x.lt y = true ↔ doubleValue x.bits < doubleValue y.bits := by
  rw [doubleValue_eq_valueOfOrderValue hx, doubleValue_eq_valueOfOrderValue hy,
    strictMonoOn_valueOfOrderValue.lt_iff_lt (orderValue_mem_Icc hx) (orderValue_mem_Icc hy)]
  simp [lt, hx, hy]

theorem le_eq_true_iff {x y : Double} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x.le y = true ↔ doubleValue x.bits ≤ doubleValue y.bits := by
  rw [doubleValue_eq_valueOfOrderValue hx, doubleValue_eq_valueOfOrderValue hy,
    strictMonoOn_valueOfOrderValue.le_iff_le (orderValue_mem_Icc hx) (orderValue_mem_Icc hy)]
  simp [le, hx, hy]

theorem beq_eq_true_iff {x y : Double} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x.beq y = true ↔ doubleValue x.bits = doubleValue y.bits := by
  rw [doubleValue_eq_valueOfOrderValue hx, doubleValue_eq_valueOfOrderValue hy,
    strictMonoOn_valueOfOrderValue.injOn.eq_iff (orderValue_mem_Icc hx) (orderValue_mem_Icc hy)]
  simp [beq, hx, hy]

theorem isNaN_eq_false_iff (x : Double) : x.isNaN = false ↔ ¬ IsNaN x.bits := by
  rw [← isNaN_iff]; simp

/-! ### The magnitude and the operations on the sign bit -/

theorem toNat_bits_eq_mod (x : Double) :
    x.bits.toNat = (if x.signBit then 2 ^ 63 else 0) + x.bits.toNat % 2 ^ 63 := by
  rw [← expField_mul_add_fracField]; exact toNat_bits x

theorem isNaN_eq_false_iff_le (x : Double) :
    x.isNaN = false ↔ x.bits.toNat % 2 ^ 63 ≤ maxOrderValue := by
  rw [← expField_mul_add_fracField, maxOrderValue]
  simp only [isNaN, Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
  lia [fracField_lt x, expField_lt x]

theorem signBit_and_mod_of_toNat_eq {x : Double} {s : Bool} {n : ℕ} (hn : n < 2 ^ 63)
    (h : x.bits.toNat = (if s then 2 ^ 63 else 0) + n) :
    x.signBit = s ∧ x.bits.toNat % 2 ^ 63 = n := by
  rw [signBit_eq_decide, h]
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.mod_eq_of_lt hn, and_true]
    simpa using hn
  · simp only [↓reduceIte, Nat.add_mod_left, Nat.mod_eq_of_lt hn, and_true]
    simp

theorem toNat_fabs (x : Double) : (fabs x).bits.toNat = x.bits.toNat % 2 ^ 63 :=
  toNat_and_mask x.bits

theorem toNat_mod_fabs (x : Double) : (fabs x).bits.toNat % 2 ^ 63 = x.bits.toNat % 2 ^ 63 := by
  rw [toNat_fabs, Nat.mod_mod]

theorem signBit_fabs (x : Double) : (fabs x).signBit = false := by
  rw [signBit_eq_decide, toNat_fabs]
  exact decide_eq_false (Nat.not_le.mpr (Nat.mod_lt _ (Nat.two_pow_pos 63)))

theorem toNat_mod_neg (x : Double) : (neg x).bits.toNat % 2 ^ 63 = x.bits.toNat % 2 ^ 63 := by
  rw [neg, UInt64.toNat_xor, Nat.xor_mod_two_pow]; simp

/-- Flipping the sign bit adds `2 ^ 63` to the bits, modulo `2 ^ 64`. -/
theorem toNat_bits_neg (x : Double) :
    (neg x).bits.toNat = (x.bits.toNat + 2 ^ 63) % 2 ^ 64 := by
  have hd : (neg x).bits.toNat / 2 ^ 63 = x.bits.toNat / 2 ^ 63 ^^^ 1 := by
    rw [neg, UInt64.toNat_xor, Nat.xor_div_two_pow]; rfl
  have hm := toNat_mod_neg x
  have h1 := x.bits.toNat_lt
  have h2 := (neg x).bits.toNat_lt
  rcases Nat.lt_or_ge x.bits.toNat (2 ^ 63) with hs | hs
  · rw [Nat.div_eq_of_lt hs, Nat.zero_xor] at hd; lia
  · rw [Nat.div_eq_of_lt_le (k := 1) (m := x.bits.toNat) (by lia) (by lia), Nat.xor_self] at hd
    lia

theorem signBit_neg (x : Double) : (neg x).signBit = !x.signBit := by
  rw [signBit_eq_decide, signBit_eq_decide, toNat_bits_neg, ← decide_not]
  exact decide_eq_decide.mpr (by lia [x.bits.toNat_lt])

theorem bits_neg (x : Double) : (neg x).bits = x.bits + 0x8000000000000000 :=
  UInt64.toNat_inj.mp (by rw [toNat_bits_neg, UInt64.toNat_add]; rfl)

protected theorem neg_neg (x : Double) : neg (neg x) = x := by
  simp only [neg, UInt64.xor_assoc, UInt64.xor_self, UInt64.xor_zero]

theorem orderValue_fabs (x : Double) :
    (fabs x).orderValue = ((x.bits.toNat % 2 ^ 63 : ℕ) : ℤ) := by
  rw [orderValue_eq_mod, signBit_fabs, toNat_mod_fabs]; rfl

theorem orderValue_neg (x : Double) : (neg x).orderValue = -x.orderValue := by
  rw [orderValue_eq_mod, orderValue_eq_mod, signBit_neg, toNat_mod_neg]
  cases x.signBit <;> simp

theorem div_mod_eq_fields (x : Double) :
    x.bits.toNat % 2 ^ 63 / 2 ^ 52 = x.expField ∧ x.bits.toNat % 2 ^ 63 % 2 ^ 52 = x.fracField :=
  (Nat.div_mod_unique (Nat.two_pow_pos 52)).mpr
    ⟨by rw [← expField_mul_add_fracField]; lia, fracField_lt x⟩

theorem expField_eq_mod (x : Double) : x.expField = x.bits.toNat % 2 ^ 63 / 2 ^ 52 :=
  (div_mod_eq_fields x).1.symm

theorem fracField_eq_mod (x : Double) : x.fracField = x.bits.toNat % 2 ^ 63 % 2 ^ 52 :=
  (div_mod_eq_fields x).2.symm

theorem expField_neg (x : Double) : (neg x).expField = x.expField := by
  rw [expField_eq_mod, expField_eq_mod, toNat_mod_neg]

theorem fracField_neg (x : Double) : (neg x).fracField = x.fracField := by
  rw [fracField_eq_mod, fracField_eq_mod, toNat_mod_neg]

theorem expField_fabs (x : Double) : (fabs x).expField = x.expField := by
  rw [expField_eq_mod, expField_eq_mod, toNat_mod_fabs]

theorem fracField_fabs (x : Double) : (fabs x).fracField = x.fracField := by
  rw [fracField_eq_mod, fracField_eq_mod, toNat_mod_fabs]

theorem isNaN_fabs (x : Double) : (fabs x).isNaN = x.isNaN := by
  simp only [isNaN, expField_fabs, fracField_fabs]

theorem isNaN_neg (x : Double) : (neg x).isNaN = x.isNaN := by
  simp only [isNaN, expField_neg, fracField_neg]

theorem isFinite_neg (x : Double) : (neg x).isFinite = x.isFinite := by
  simp only [isFinite, expField_neg]

theorem isFinite_fabs (x : Double) : (fabs x).isFinite = x.isFinite := by
  simp only [isFinite, expField_fabs]

theorem toRat_neg (x : Double) : (neg x).toRat = -x.toRat := by
  rw [toRat_eq_fields, toRat_eq_fields, signBit_neg, expField_neg, fracField_neg]
  cases x.signBit <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    neg_one_mul, one_mul, neg_neg]

theorem toRat_fabs (x : Double) : (fabs x).toRat = |x.toRat| := by
  have h0 : 0 ≤ if x.expField = 0 then (x.fracField : ℚ) * 2 ^ (-1074 : ℤ)
      else (2 ^ 52 + x.fracField) * 2 ^ ((x.expField : ℤ) - 1075) := by
    split_ifs <;> exact mul_nonneg (by positivity) (zpow_nonneg zero_le_two _)
  rw [toRat_eq_fields, toRat_eq_fields, signBit_fabs, expField_fabs, fracField_fabs]
  cases x.signBit <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul, one_mul, abs_neg,
    abs_of_nonneg h0]

/-! ### Doubles from their fields -/

theorem toNat_sign_or {neg : Bool} {n : ℕ} (hn : n < 2 ^ 63) :
    ((if neg then 0x8000000000000000 else 0 : UInt64) ||| n.toUInt64).toNat =
      (if neg then 2 ^ 63 else 0) + n := by
  rw [UInt64.toNat_or, Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  cases neg
  · simp
  · simp only [↓reduceIte]
    rw [show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl, Nat.or_comm,
      Nat.or_two_pow_eq_add_of_lt hn, Nat.add_comm]

theorem shiftLeft_or_eq {E F : ℕ} (hE : E < 2048) (hF : F < 2 ^ 52) :
    (E.toUInt64 <<< 52 ||| F.toUInt64) = (E * 2 ^ 52 + F).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [Nat.toUInt64_eq, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat']
  rw [show (52 : UInt64).toNat % 64 = 52 from rfl, Nat.mod_eq_of_lt (by lia : E < 2 ^ 64),
    Nat.mod_eq_of_lt (by lia : F < 2 ^ 64), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by lia),
    Nat.mod_eq_of_lt (by lia), Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt hF]

theorem toNat_sign_or_or {neg : Bool} {E F : ℕ} (hE : E < 2048) (hF : F < 2 ^ 52) :
    ((if neg then 0x8000000000000000 else 0 : UInt64) ||| E.toUInt64 <<< 52 ||| F.toUInt64).toNat =
      (if neg then 2 ^ 63 else 0) + (E * 2 ^ 52 + F) := by
  rw [UInt64.or_assoc, shiftLeft_or_eq hE hF, toNat_sign_or (by lia)]

theorem toRat_of_toNat_eq {x : Double} {neg : Bool} {E F : ℕ} (hE : E < 2047) (hF : F < 2 ^ 52)
    (h : x.bits.toNat = (if neg then 2 ^ 63 else 0) + (E * 2 ^ 52 + F)) :
    x.isFinite = true ∧ x.signBit = neg ∧ x.toRat = (if neg then -1 else 1) *
      (if E = 0 then (F : ℚ) * 2 ^ (-1074 : ℤ) else (2 ^ 52 + F) * 2 ^ ((E : ℤ) - 1075)) := by
  obtain ⟨h1, h2, h3⟩ := fields_eq_of_toNat_bits_eq (by lia) hF h
  refine ⟨by simp [isFinite, h2]; lia, h1, ?_⟩
  rw [toRat_eq_fields, h1, h2, h3]

theorem roundShift_of_nonpos {m : ℕ} {k : ℤ} (hk : k ≤ 0) :
    roundShift m k = m * 2 ^ (-k).toNat := by
  simp [roundShift, hk, Nat.shiftLeft_eq]

/-! ### The assembly of the bits -/

theorem ofSignificand_of_ne {neg : Bool} {M : ℕ} (q : ℤ) (h : M ≠ 2 ^ 53) :
    ofSignificand neg M q = assemble neg M q := by
  simp only [ofSignificand, h, ↓reduceIte]

theorem ofSignificand_two_pow (neg : Bool) (q : ℤ) :
    ofSignificand neg (2 ^ 53) q = assemble neg (2 ^ 52) (q + 1) := by
  simp only [ofSignificand, ↓reduceIte]

/-- The sign bit, the exponent field and the fraction of the double that
`Ratpoints.Double.assemble` makes from a significand `M < 2 ^ 53` and the exponent `q` of its last
place: those of a subnormal or a zero for `M < 2 ^ 52`, of an infinity when the exponent field
`q + 1075` would reach `2047`, and of a normal double otherwise. -/
theorem fields_assemble (neg : Bool) {M : ℕ} (q : ℤ) (hM : M < 2 ^ 53) :
    (assemble neg M q).signBit = neg ∧
      (assemble neg M q).expField =
        (if M < 2 ^ 52 then 0 else if 2047 ≤ q + 1075 then 2047 else (q + 1075).toNat) ∧
      (assemble neg M q).fracField =
        if M < 2 ^ 52 then M else if 2047 ≤ q + 1075 then 0 else M - 2 ^ 52 := by
  by_cases h1 : M < 2 ^ 52
  · simp only [h1, ↓reduceIte]
    refine fields_eq_of_toNat_bits_eq (by decide) h1 ?_
    simp only [assemble, h1, ↓reduceIte]
    rw [toNat_sign_or (by lia)]; simp
  by_cases h2 : 2047 ≤ q + 1075
  · simp only [h1, h2, ↓reduceIte]
    refine fields_eq_of_toNat_bits_eq (by decide) (by decide) ?_
    simp only [assemble, h1, h2, ↓reduceIte]
    exact toNat_sign_or (n := 2047 * 2 ^ 52 + 0) (by norm_num)
  · simp only [h1, h2, ↓reduceIte]
    refine fields_eq_of_toNat_bits_eq (by lia) (by lia) ?_
    simp only [assemble, h1, h2, ↓reduceIte]
    exact toNat_sign_or_or (by lia) (by lia)

theorem isFinite_assemble_iff {neg : Bool} {M : ℕ} {q : ℤ} (hM : M < 2 ^ 53) :
    (assemble neg M q).isFinite = true ↔ M < 2 ^ 52 ∨ q + 1075 < 2047 := by
  obtain ⟨-, he, -⟩ := fields_assemble neg q hM
  simp only [isFinite, he]
  split_ifs <;> simp <;> lia

/-- The value `±M 2 ^ q` of the double that `Ratpoints.Double.assemble` makes from a significand
`M < 2 ^ 53` and the exponent `q` of its last place in the range of the finite doubles: `q = -1074`
for a subnormal or a zero (`M < 2 ^ 52`), and `-1074 ≤ q` with the exponent field `q + 1075` below
`2047` for a normal double. -/
theorem toRat_assemble {neg : Bool} {M : ℕ} {q : ℤ} (hM : M < 2 ^ 53)
    (hsub : M < 2 ^ 52 → q = -1074) (hnorm : 2 ^ 52 ≤ M → -1074 ≤ q ∧ q + 1075 < 2047) :
    (assemble neg M q).toRat = (if neg then -1 else 1) * ((M : ℚ) * 2 ^ q) := by
  obtain ⟨hs, he, hf⟩ := fields_assemble neg q hM
  rw [toRat_eq_fields, hs, he, hf]
  by_cases h1 : M < 2 ^ 52
  · simp only [h1, ↓reduceIte, hsub h1]
  obtain ⟨hq1, hq2⟩ := hnorm (by lia)
  simp only [h1, show ¬2047 ≤ q + 1075 by lia, ↓reduceIte, show (q + 1075).toNat ≠ 0 by lia]
  rw [Int.toNat_of_nonneg (by lia), Nat.cast_sub (by lia)]
  simp only [Nat.cast_pow, Nat.cast_ofNat, add_sub_cancel, add_sub_cancel_right]

theorem mul_two_pow_lt_two_pow_53 {m t : ℕ} (ht : m.log2 + t ≤ 52) : m * 2 ^ t < 2 ^ 53 := by
  calc m * 2 ^ t < 2 ^ (m.log2 + 1) * 2 ^ t :=
        Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)
    _ = 2 ^ (m.log2 + 1 + t) := (Nat.pow_add ..).symm
    _ ≤ 2 ^ 53 := Nat.pow_le_pow_right (by decide) (by lia)

theorem two_pow_le_mul_two_pow {m t : ℕ} (hm0 : m ≠ 0) (ht : m.log2 + t = 52) :
    2 ^ 52 ≤ m * 2 ^ t :=
  calc 2 ^ 52 = 2 ^ m.log2 * 2 ^ t := by rw [← Nat.pow_add, ht]
    _ ≤ m * 2 ^ t := Nat.mul_le_mul_right _ (Nat.log2_self_le hm0)

theorem natCast_mul_two_pow_mul_zpow (m : ℕ) {e q : ℤ} (h : q ≤ e) :
    ((m * 2 ^ (e - q).toNat : ℕ) : ℚ) * 2 ^ q = m * 2 ^ e := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (by lia),
    mul_assoc, ← zpow_add₀ two_ne_zero, sub_add_cancel]

theorem ofDyadic_exact {neg : Bool} {m : ℕ} {e : ℤ} (hm0 : m ≠ 0) (hm : m < 2 ^ 53)
    (he : -1074 ≤ e) (he' : (m.log2 : ℤ) + e ≤ 1023) :
    (ofDyadic neg m e).isFinite = true ∧ (ofDyadic neg m e).signBit = neg ∧
      (ofDyadic neg m e).toRat = (if neg then -1 else 1) * ((m : ℚ) * 2 ^ e) := by
  have hl : m.log2 < 53 := (Nat.log2_lt hm0).mpr hm
  have hq1 := le_max_left ((m.log2 : ℤ) + e - 52) (-1074)
  have hq2 := le_max_right ((m.log2 : ℤ) + e - 52) (-1074)
  have hq3 := max_choice ((m.log2 : ℤ) + e - 52) (-1074)
  simp only [ofDyadic, hm0, ↓reduceIte, roundShift_of_nonpos
    (by lia : max ((m.log2 : ℤ) + e - 52) (-1074) - e ≤ 0), neg_sub]
  generalize max ((m.log2 : ℤ) + e - 52) (-1074) = q at hq1 hq2 hq3 ⊢
  have hM : m * 2 ^ (e - q).toNat < 2 ^ 53 := mul_two_pow_lt_two_pow_53 (by lia)
  rw [ofSignificand_of_ne q hM.ne]
  have hsub (h : m * 2 ^ (e - q).toNat < 2 ^ 52) : q = -1074 := by
    by_contra hq
    lia [two_pow_le_mul_two_pow hm0 (t := (e - q).toNat) (by lia)]
  refine ⟨(isFinite_assemble_iff hM).mpr (.inr (by lia)), (fields_assemble neg q hM).1, ?_⟩
  rw [toRat_assemble hM hsub fun _ ↦ ⟨hq2, by lia⟩, natCast_mul_two_pow_mul_zpow m (by lia)]

/-! ### The neighbours -/

theorem isZero_eq_decide (x : Double) : x.isZero = decide (x.bits.toNat % 2 ^ 63 = 0) := by
  simp only [isZero]
  refine decide_eq_decide.mpr ?_
  rw [← UInt64.toNat_inj, toNat_and_mask]
  rfl

theorem toNat_huge : huge.bits.toNat = maxOrderValue := rfl

/-! ### The conversions -/

theorem toDyadic_bounds (x : Double) :
    x.toDyadic.1.natAbs < 2 ^ 53 ∧ -1074 ≤ x.toDyadic.2 ∧ x.toDyadic.2 ≤ 972 := by
  have hF := fracField_lt x
  have hE := expField_lt x
  rw [toDyadic_eq]
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> simp <;> lia

theorem toDyadic_fst_eq (x : Double) :
    x.toDyadic.1 = (if x.signBit then -1 else 1) * (x.toDyadic.1.natAbs : ℤ) := by
  rw [toDyadic_eq]
  dsimp only
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  split_ifs <;> simp

theorem isZero_eq_true_iff {x : Double} : x.isZero = true ↔ x.toRat = 0 := by
  rw [isZero_eq_decide, decide_eq_true_eq, ← expField_mul_add_fracField, toRat_eq_fields]
  refine ⟨fun h ↦ by rw [show x.expField = 0 by lia, show x.fracField = 0 by lia]; simp, fun h ↦ ?_⟩
  have h1 : (if x.signBit then (-1 : ℚ) else 1) ≠ 0 := by split_ifs <;> norm_num
  have h2 := (mul_eq_zero.mp h).resolve_left h1
  split_ifs at h2 with hE
  · rw [hE]; simpa using h2
  · exact absurd h2 (mul_ne_zero (by positivity) (zpow_ne_zero _ two_ne_zero))

theorem isZero_eq_false_iff {x : Double} : x.isZero = false ↔ x.toRat ≠ 0 := by
  rw [ne_eq, ← isZero_eq_true_iff, Bool.not_eq_true]

theorem toNat_shift_eq_floor (m : ℕ) (e : ℤ) :
    (if 0 ≤ e then m <<< e.toNat else m >>> (-e).toNat) = ⌊(m : ℚ) * 2 ^ e⌋₊ := by
  split_ifs with he
  · rw [Nat.shiftLeft_eq, ← Int.toNat_of_nonneg he, zpow_natCast, Int.toNat_of_nonneg he]
    exact_mod_cast (Nat.floor_natCast (R := ℚ) _).symm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = -(k : ℤ) := ⟨(-e).toNat, by lia⟩
    rw [Nat.shiftRight_eq_div_pow, zpow_neg, zpow_natCast, ← div_eq_mul_inv,
      show ((2 : ℚ) ^ k) = ((2 ^ k : ℕ) : ℚ) by push_cast; rfl, Nat.floor_div_eq_div]
    simp

theorem toDyadic_fst_nonneg {x : Double} (h0 : 0 ≤ x.toRat) : 0 ≤ x.toDyadic.1 := by
  have hr := toRat_eq x
  by_contra hm
  have : (x.toDyadic.1 : ℚ) * 2 ^ x.toDyadic.2 < 0 :=
    mul_neg_of_neg_of_pos (mod_cast not_le.mp hm) (zpow_pos two_pos _)
  linarith

/-- The truncation of the magnitude of `Ratpoints.Double.toDyadic x = (m, e)` that the conversions
compute is the floor of a double `x ≥ 0`. -/
theorem shift_eq_floor_toRat {x : Double} (h0 : 0 ≤ x.toRat) {m e : ℤ} (hd : x.toDyadic = (m, e)) :
    (if 0 ≤ e then m.natAbs <<< e.toNat else m.natAbs >>> (-e).toNat) = ⌊x.toRat⌋₊ := by
  have hm := toDyadic_fst_nonneg h0
  rw [hd] at hm
  rw [toNat_shift_eq_floor, toRat_eq, hd, Nat.cast_natAbs, Int.cast_abs,
    abs_of_nonneg (mod_cast hm)]

theorem toNat_toUInt64 {x : Double} (h0 : 0 ≤ x.toRat) (h1 : x.toRat < 2 ^ 64) :
    (toUInt64 x).toNat = ⌊x.toRat⌋₊ := by
  rcases hd : x.toDyadic with ⟨m, e⟩
  simp only [toUInt64, hd]
  rw [shift_eq_floor_toRat h0 hd, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
  exact (Nat.floor_lt h0).mpr (mod_cast h1)

theorem toInt_toInt64 {x : Double} (h0 : 0 ≤ x.toRat) (h1 : x.toRat < 2 ^ 63) :
    x.toInt64.toInt = ⌊x.toRat⌋₊ := by
  have hm := toDyadic_fst_nonneg h0
  rcases hd : x.toDyadic with ⟨m, e⟩
  rw [hd] at hm
  have hf : ⌊x.toRat⌋₊ < 2 ^ 63 := (Nat.floor_lt h0).mpr (mod_cast h1)
  simp only [toInt64, hd, show ¬m < 0 by lia, ↓reduceIte]
  rw [shift_eq_floor_toRat h0 hd, Int64.toInt_ofInt_of_le (by lia) (by lia)]

theorem isNaN_eq_false_of_isFinite {x : Double} (hx : x.isFinite = true) : x.isNaN = false := by
  simp only [isFinite, bne_iff_ne, ne_eq] at hx
  simp [isNaN, hx]

theorem isInf_eq_false_of_isFinite {x : Double} (hx : x.isFinite = true) : x.isInf = false := by
  simp only [isFinite, bne_iff_ne, ne_eq] at hx
  simp [isInf, hx]

theorem abs_toRat (x : Double) : |x.toRat| = x.toDyadic.1.natAbs * 2 ^ x.toDyadic.2 := by
  rw [toRat_eq, abs_mul, abs_of_pos (zpow_pos (two_pos (α := ℚ)) x.toDyadic.2), Nat.cast_natAbs,
    Int.cast_abs]

theorem lt_add_of_two_pow_le_mul {a : ℕ} {k L : ℤ} (ha : a < 2 ^ 53)
    (h : (2 : ℚ) ^ L ≤ a * 2 ^ k) : L < 53 + k := by
  have : (a : ℚ) * 2 ^ k < 2 ^ (53 + k) := by
    rw [zpow_add₀ two_ne_zero]
    exact mul_lt_mul_of_pos_right (mod_cast ha) (zpow_pos two_pos _)
  exact (zpow_lt_zpow_iff_right₀ one_lt_two).mp (lt_of_le_of_lt h this)

theorem two_zpow_log2_le_mul {m : ℕ} (hm : m ≠ 0) (e : ℤ) :
    (2 : ℚ) ^ ((m.log2 : ℤ) + e) ≤ m * 2 ^ e ∧ (m : ℚ) * 2 ^ e < 2 ^ ((m.log2 : ℤ) + 1 + e) := by
  have h1 : (2 : ℚ) ^ m.log2 ≤ m := mod_cast Nat.log2_self_le hm
  have h2 : (m : ℚ) < 2 ^ (m.log2 + 1) := mod_cast Nat.lt_log2_self
  have ht : (0 : ℚ) < 2 ^ e := zpow_pos two_pos _
  rw [zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, ← zpow_natCast,
    show ((m.log2 : ℤ) + 1) = ((m.log2 + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  exact ⟨mul_le_mul_of_nonneg_right h1 ht.le, mul_lt_mul_of_pos_right h2 ht⟩

theorem log2_add_lt_of_mul_lt {a : ℕ} {k L : ℤ} (ha : a ≠ 0)
    (h : (a : ℚ) * 2 ^ k < 2 ^ L) : (a.log2 : ℤ) + k < L :=
  (zpow_lt_zpow_iff_right₀ one_lt_two).mp ((two_zpow_log2_le_mul ha k).1.trans_lt h)

theorem ldexp_eq {x : Double} (hx : x.isFinite = true) (hx0 : x.toRat ≠ 0) (n : ℤ) :
    ldexp x n = ofDyadic x.signBit x.toDyadic.1.natAbs (x.toDyadic.2 + n) := by
  simp only [ldexp, isNaN_eq_false_of_isFinite hx, isInf_eq_false_of_isFinite hx,
    isZero_eq_false_iff.mpr hx0, Bool.or_false, Bool.false_eq_true, ↓reduceIte]

theorem natAbs_toDyadic_fst_ne_zero {x : Double} (hx0 : x.toRat ≠ 0) :
    x.toDyadic.1.natAbs ≠ 0 := fun h ↦ hx0 <| by
  rw [toRat_eq, Int.natAbs_eq_zero.mp h]; simp

/-- The value `±|m| 2 ^ (e + k)` of a double with the sign of `x` and the magnitude of
`Ratpoints.Double.toDyadic x = (m, e)` scaled by `2 ^ k` is `x 2 ^ k`. -/
theorem sign_mul_natAbs_mul_zpow (x : Double) (k : ℤ) :
    (if x.signBit then -1 else 1) * ((x.toDyadic.1.natAbs : ℚ) * 2 ^ (x.toDyadic.2 + k)) =
      x.toRat * 2 ^ k := by
  rw [toRat_eq x, zpow_add₀ two_ne_zero]
  conv_rhs => rw [toDyadic_fst_eq x]
  rw [Nat.cast_natAbs, Int.cast_abs]
  split_ifs <;> push_cast <;> ring

theorem ldexp_exact {x : Double} {n : ℤ} (hx : x.isFinite = true) (hx0 : x.toRat ≠ 0)
    (hlo : (2 : ℚ) ^ (-1022 : ℤ) ≤ |x.toRat| * 2 ^ n) (hhi : |x.toRat| * 2 ^ n < 2 ^ (1023 : ℤ)) :
    (ldexp x n).isFinite = true ∧ (ldexp x n).signBit = x.signBit ∧
      (ldexp x n).toRat = x.toRat * 2 ^ n := by
  obtain ⟨hm53, he, -⟩ := toDyadic_bounds x
  have hm0 := natAbs_toDyadic_fst_ne_zero hx0
  rw [abs_toRat, mul_assoc, ← zpow_add₀ two_ne_zero] at hlo hhi
  obtain ⟨h1, h2, h3⟩ := ofDyadic_exact (neg := x.signBit) (e := x.toDyadic.2 + n) hm0 hm53
    (by lia [lt_add_of_two_pow_le_mul hm53 hlo]) (by lia [log2_add_lt_of_mul_lt hm0 hhi])
  rw [ldexp_eq hx hx0]
  exact ⟨h1, h2, by rw [h3, sign_mul_natAbs_mul_zpow]⟩

theorem ofInt64_exact_of_lt {n : Int64} (hn : n.toInt.natAbs < 2 ^ 53) :
    (ofInt64 n).isFinite = true ∧ (ofInt64 n).toRat = n.toInt := by
  rcases eq_or_ne n.toInt.natAbs 0 with h0 | h0
  · have hn0 : n.toInt = 0 := Int.natAbs_eq_zero.mp h0
    have : decide (n < 0) = false := by simp [Int64.lt_iff_toInt_lt, hn0]
    simp only [ofInt64, ofDyadic, this, Bool.false_eq_true, ↓reduceIte, hn0]
    exact ⟨by decide, by rw [isZero_eq_true_iff.mp (by decide)]; simp⟩
  · have hl : n.toInt.natAbs.log2 < 53 := (Nat.log2_lt h0).mpr hn
    obtain ⟨h1, -, h3⟩ := ofDyadic_exact (neg := decide (n < 0)) (e := 0) h0 hn (by lia) (by lia)
    refine ⟨h1, ?_⟩
    rw [ofInt64, h3, zpow_zero, mul_one, Nat.cast_natAbs, Int.cast_abs]
    by_cases h : n < 0
    · have : n.toInt < 0 := Int64.lt_iff_toInt_lt.mp h
      simp [h, abs_of_neg (show (n.toInt : ℚ) < 0 from mod_cast this)]
    · have : 0 ≤ n.toInt := by simpa [Int64.lt_iff_toInt_lt] using h
      simp [h, abs_of_nonneg (show (0 : ℚ) ≤ n.toInt from mod_cast this)]

/-- `(double)n` is exact for `|n| ≤ 2 ^ 53`. -/
theorem ofInt64_exact {n : Int64} (hn : n.toInt.natAbs ≤ 2 ^ 53) :
    (ofInt64 n).isFinite = true ∧ (ofInt64 n).toRat = n.toInt := by
  rcases Nat.lt_or_eq_of_le hn with h | h
  · exact ofInt64_exact_of_lt h
  · rcases Int.natAbs_eq n.toInt with h' | h' <;> rw [h] at h'
    · rw [show n = 2 ^ 53 from Int64.toInt_inj.mp (by rw [h']; rfl)]; decide
    · rw [show n = -2 ^ 53 from Int64.toInt_inj.mp (by rw [h']; rfl)]; decide

/-! ### The ends of the search intervals -/

theorem le_eq_true_iff' {x y : Double} :
    x.le y = true ↔ ¬ IsNaN x.bits ∧ ¬ IsNaN y.bits ∧ doubleValue x.bits ≤ doubleValue y.bits := by
  rw [← isNaN_eq_false_iff, ← isNaN_eq_false_iff]
  by_cases hx : x.isNaN = false
  · by_cases hy : y.isNaN = false
    · rw [le_eq_true_iff hx hy]; simp [hx, hy]
    · simp_all [le]
  · simp_all [le]

theorem lt_eq_true_iff' {x y : Double} :
    x.lt y = true ↔ ¬ IsNaN x.bits ∧ ¬ IsNaN y.bits ∧ doubleValue x.bits < doubleValue y.bits := by
  rw [← isNaN_eq_false_iff, ← isNaN_eq_false_iff]
  by_cases hx : x.isNaN = false
  · by_cases hy : y.isNaN = false
    · rw [lt_eq_true_iff hx hy]; simp [hx, hy]
    · simp_all [lt]
  · simp_all [lt]

/-- A finite double of absolute value at least `2 ^ 52` is an integer: its exponent is not
negative. -/
theorem toDyadic_snd_nonneg {x : Double} (h : 2 ^ 52 ≤ |x.toRat|) : 0 ≤ x.toDyadic.2 := by
  obtain ⟨hm, -, -⟩ := toDyadic_bounds x
  rw [abs_toRat] at h
  have h' : (2 : ℚ) ^ (52 : ℤ) ≤ x.toDyadic.1.natAbs * 2 ^ x.toDyadic.2 := mod_cast h
  lia [lt_add_of_two_pow_le_mul hm h']

theorem toRat_eq_natCast_floor {x : Double} (h : 2 ^ 52 ≤ x.toRat) :
    x.toRat = (⌊x.toRat⌋₊ : ℚ) := by
  have h0 : 0 ≤ x.toRat := le_trans (by norm_num) h
  have he := toDyadic_snd_nonneg (h.trans (le_abs_self _))
  have hm := toDyadic_fst_nonneg h0
  have hc : ((x.toDyadic.1.toNat : ℕ) : ℚ) = x.toDyadic.1 := mod_cast Int.toNat_of_nonneg hm
  rw [toRat_eq, ← Int.toNat_of_nonneg he, zpow_natCast, ← hc, ← Nat.cast_ofNat, ← Nat.cast_pow,
    ← Nat.cast_mul, Nat.floor_natCast]

theorem toRat_nonneg {x : Double} (hs : x.signBit = false) : 0 ≤ x.toRat := by
  rw [toRat_eq_fields, hs]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  split_ifs <;> exact mul_nonneg (by positivity) (zpow_nonneg zero_le_two _)

theorem lt_zero_eq_true_iff {x : Double} (hx : x.isNaN = false) :
    x.lt .zero = true ↔ x.orderValue < 0 := by
  simp [lt, hx, show zero.isNaN = false by decide, show zero.orderValue = 0 by decide]

theorem lt_twoPow63_eq_true_iff {x : Double} (hx : x.isNaN = false) :
    x.lt .twoPow63 = true ↔ x.orderValue < 0x43e0000000000000 := by
  simp [lt, hx, show twoPow63.isNaN = false by decide,
    show twoPow63.orderValue = 0x43e0000000000000 by decide]

/-- A double whose absolute value is not below `2 ^ 63` (`|x| < 2 ^ 63` false in the C code) has a
value of at least `2 ^ 63` or at most `-2 ^ 63`, by its sign. -/
theorem le_doubleValue_or_of_lt_eq_false {x : Double} (hx : x.isNaN = false)
    (h : x.fabs.lt .twoPow63 = false) :
    (x.lt .zero = false ∧ (((2 ^ 63 : ℚ)) : WithBotTop ℚ) ≤ doubleValue x.bits) ∨
      (x.lt .zero = true ∧ doubleValue x.bits ≤ (((-2 ^ 63 : ℚ)) : WithBotTop ℚ)) := by
  have hk := natAbs_orderValue_le hx
  rw [← Bool.not_eq_true, lt_twoPow63_eq_true_iff (by rw [isNaN_fabs]; exact hx),
    orderValue_fabs] at h
  have e1 : doubleValue twoPow63.bits = (((2 ^ 63 : ℚ)) : WithBotTop ℚ) := by decide +kernel
  have e2 : doubleValue twoPow63.neg.bits = (((-2 ^ 63 : ℚ)) : WithBotTop ℚ) := by decide +kernel
  have m1 := orderValue_mem_Icc (x := twoPow63) (by decide)
  have m2 := orderValue_mem_Icc (x := twoPow63.neg) (by decide)
  rw [doubleValue_eq_valueOfOrderValue (by decide)] at e1 e2
  have o1 : twoPow63.orderValue = 0x43e0000000000000 := by decide
  have o2 : twoPow63.neg.orderValue = -0x43e0000000000000 := by decide
  have hov := orderValue_eq_mod x
  rw [doubleValue_eq_valueOfOrderValue hx, ← e1, ← e2]
  cases hsb : x.signBit <;> simp only [hsb, Bool.false_eq_true, ↓reduceIte] at hov
  · refine .inl ⟨by rw [← Bool.not_eq_true, lt_zero_eq_true_iff hx]; lia, ?_⟩
    rw [strictMonoOn_valueOfOrderValue.le_iff_le m1 (orderValue_mem_Icc hx)]; lia
  · refine .inr ⟨by rw [lt_zero_eq_true_iff hx]; lia, ?_⟩
    rw [strictMonoOn_valueOfOrderValue.le_iff_le (orderValue_mem_Icc hx) m2]; lia

theorem isFinite_and_abs_lt_of_lt {x : Double} (h : x.fabs.lt .twoPow63 = true) :
    x.isFinite = true ∧ |x.toRat| < 2 ^ 63 := by
  have hn : x.fabs.isNaN = false := by simp_all [lt]
  have hf : x.isFinite = true := by
    rw [lt_twoPow63_eq_true_iff hn, orderValue_fabs] at h
    simp only [isFinite, expField_eq_mod, bne_iff_ne, ne_eq]
    have : x.bits.toNat % 2 ^ 63 / 2 ^ 52 < 1086 := Nat.div_lt_of_lt_mul (by lia)
    lia
  refine ⟨hf, ?_⟩
  rwa [lt_eq_true_iff hn (by decide), doubleValue_eq_toRat (isFinite_fabs x ▸ hf),
    doubleValue_eq_toRat (by decide), toRat_fabs, show twoPow63.toRat = 2 ^ 63 by decide,
    WithBotTop.coe_lt_coe] at h

theorem lt_twoPow63_eq_true_iff_toRat {x : Double} (hf : x.isFinite = true) :
    x.lt .twoPow63 = true ↔ x.toRat < 2 ^ 63 := by
  rw [lt_eq_true_iff (isNaN_eq_false_of_isFinite hf) (by decide), doubleValue_eq_toRat hf,
    doubleValue_eq_toRat (by decide), show twoPow63.toRat = 2 ^ 63 by decide,
    WithBotTop.coe_lt_coe]

theorem lt_zero_eq_true_iff_toRat {x : Double} (hf : x.isFinite = true) :
    x.lt .zero = true ↔ x.toRat < 0 := by
  rw [lt_eq_true_iff (isNaN_eq_false_of_isFinite hf) (by decide), doubleValue_eq_toRat hf,
    doubleValue_eq_toRat (by decide), isZero_eq_true_iff.mp (show zero.isZero = true by decide),
    WithBotTop.coe_lt_coe]

/-- A double `0 ≤ x < 2 ^ 63` whose conversion to a `long` is not below `H` is at least `H`. -/
theorem le_toRat_of_not_toInt64_lt {x : Double} (h0 : 0 ≤ x.toRat) (h63 : x.toRat < 2 ^ 63)
    {H : ℕ} (hH63 : H < 2 ^ 63) (h : ¬x.toInt64 < H.toInt64) : (H : ℚ) ≤ x.toRat := by
  rw [Int64.lt_iff_toInt_lt, Int64.toInt_ofNat_of_lt hH63, toInt_toInt64 h0 h63, not_lt] at h
  exact (Nat.cast_le.mpr (mod_cast h)).trans (Nat.floor_le h0)

end Double

end Ratpoints

end
