/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Proof.Double

import Mathlib.Algebra.Order.Field.Power
import LeanPool.Ratpoints.Mathlib.Order.WithBotTop

/-!
# The rounding of the doubles of the model

`Ratpoints.Double.ofRatio` and `Ratpoints.Double.ofDyadic`, the doubles nearest to `±n / d` and to
`±m 2 ^ e`, which `strtod` and the conversions of the model compute, are never a NaN
(`Ratpoints.Double.isNaN_ofRatio`, `Ratpoints.Double.isNaN_ofDyadic`), and a finite result is a
faithful rounding: the number lies strictly between the neighbours `nextDown x` and `nextUp x` of
the result `x` (`Ratpoints.Double.lt_nextUp_and_nextDown_lt_ofRatio`,
`Ratpoints.Double.lt_nextUp_and_nextDown_lt_ofDyadic`), so that no double other than `x` lies
between `x` and the number. This is what the program needs of `strtod`: the end of a search
interval that it moves outward to a double from the double that `strtod` reads lands on the
nearest double on its side. The successor of the double of a height bound `1 ≤ H < 2 ^ 63` is
finite and above `H` (`Ratpoints.Double.isFinite_ofInt64_and_lt_toRat_nextUp`), which gives the
bound `h` of the default search interval `[-h, h]`
(`Ratpoints.Double.isFinite_and_le_toRat_ofInt64_nextUp`).

The proof goes through the significand `M` and the exponent `q` of its last place that both
functions round to, `M 2 ^ q` within half a unit `2 ^ (q - 1)` of the number
(`Ratpoints.Double.ofRatio_rounding`, `Ratpoints.Double.ofDyadic_rounding`), and the last step that
both take, the carry at `2 ^ 53` and the bits of the double (`Ratpoints.Double.ofSignificand` and
`Ratpoints.Double.assemble` of the model, the fields of the result by
`Ratpoints.Double.fields_assemble`), whose neighbours have the values of the magnitudes next to that
of the result, in units of `2 ^ (-1074)` (`Ratpoints.Double.magnitudeUnits_fields_succ`,
`Ratpoints.Double.lt_nextUp_and_nextDown_lt`).

## Main definitions

* `Ratpoints.Double.roundDiv`, `Ratpoints.Double.ratioExponent`, `Ratpoints.Double.ratioPair`,
  `Ratpoints.Double.ratioLast`: the rounding of a quotient and the exponents of
  `Ratpoints.Double.ofRatio`.

## Main statements

* `Ratpoints.Double.lt_nextUp_and_nextDown_lt_ofRatio`,
  `Ratpoints.Double.lt_nextUp_and_nextDown_lt_ofDyadic`: the faithful rounding.
* `Ratpoints.Double.isNaN_ofRatio`, `Ratpoints.Double.isNaN_ofDyadic`: no NaN.
* `Ratpoints.Double.isFinite_and_le_toRat_ofInt64_nextUp`: the double of `1 ≤ H < 2 ^ 63`, moved
  up to the next double when it is below `2 ^ 63` and its conversion to a `long` below `H`, is
  finite and at least `H`.
-/

@[expose] public section

namespace Ratpoints

namespace Double

/-! ### The neighbours of a finite double -/

/-- The units of `2 ^ (-1074)` between the values of the consecutive magnitudes with the
exponent field `E` and the fraction `F` and the next: `2 ^ (E - 1)` for `E ≥ 1`, and `1` for
`E = 0`, also where the fraction carries into the exponent. -/
theorem magnitudeUnits_fields_succ {E F : ℕ} (hF : F < 2 ^ 52) :
    magnitudeUnits (E * 2 ^ 52 + F + 1) = magnitudeUnits (E * 2 ^ 52 + F) + 2 ^ (max E 1 - 1) := by
  rw [magnitudeUnits_fields hF]
  by_cases hF1 : F + 1 < 2 ^ 52
  · rw [Nat.add_assoc, magnitudeUnits_fields hF1]
    split_ifs with h0
    · simp [h0]
    · rw [show max E 1 - 1 = E - 1 by lia]; ring
  · rw [show E * 2 ^ 52 + F + 1 = (E + 1) * 2 ^ 52 + 0 by lia, magnitudeUnits_fields (by decide),
      show F = 2 ^ 52 - 1 by lia]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    split_ifs with h0
    · simp [h0]
    · rw [show max E 1 - 1 = E - 1 by lia, show E = E - 1 + 1 by lia, pow_succ]
      simp only [Nat.add_sub_cancel]
      ring

theorem valueOfOrderValue_maxOrderValue : valueOfOrderValue maxOrderValue = ⊤ := by
  simp [valueOfOrderValue, maxOrderValue]

theorem valueOfOrderValue_neg_maxOrderValue : valueOfOrderValue (-(maxOrderValue : ℤ)) = ⊥ := by
  simp [valueOfOrderValue]

theorem expField_mul_add_fracField_lt {x : Double} (hf : x.isFinite = true) :
    x.expField * 2 ^ 52 + x.fracField < maxOrderValue := by
  simp only [isFinite, bne_iff_ne, ne_eq] at hf
  rw [maxOrderValue]; lia [fracField_lt x, expField_lt x]

theorem ne_huge_of_isFinite {x : Double} (hf : x.isFinite = true) :
    x.bits ≠ huge.bits ∧ x.bits ≠ huge.neg.bits := by
  have h := expField_mul_add_fracField_lt hf
  rw [expField_mul_add_fracField] at h
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩ <;> rw [h'] at h
  · rw [toNat_huge, Nat.mod_eq_of_lt (by simp [maxOrderValue])] at h; lia
  · rw [toNat_huge_neg] at h; simp [maxOrderValue] at h

theorem lt_valueOfOrderValue_add_one {k : ℕ} {v : ℚ} (hk : k < maxOrderValue)
    (h : v < (magnitudeUnits (k + 1) : ℚ) * 2 ^ (-1074 : ℤ)) :
    (v : WithBotTop ℚ) < valueOfOrderValue (k + 1) := by
  rcases (show k + 1 < maxOrderValue ∨ k + 1 = maxOrderValue by lia) with h' | h'
  · rwa [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      valueOfOrderValue_natCast h', WithBotTop.coe_lt_coe]
  · rw [show (k : ℤ) + 1 = (maxOrderValue : ℤ) by lia, valueOfOrderValue_maxOrderValue]
    exact WithBotTop.coe_lt_top _

theorem valueOfOrderValue_neg_sub_one_lt {k : ℕ} {v : ℚ} (hk : k < maxOrderValue)
    (h : v < (magnitudeUnits (k + 1) : ℚ) * 2 ^ (-1074 : ℤ)) :
    valueOfOrderValue (-(k : ℤ) - 1) < ((-v : ℚ) : WithBotTop ℚ) := by
  rcases (show k + 1 < maxOrderValue ∨ k + 1 = maxOrderValue by lia) with h' | h'
  · rwa [show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring,
      valueOfOrderValue_neg_natCast h', WithBotTop.coe_lt_coe, neg_lt_neg_iff]
  · rw [show -(k : ℤ) - 1 = -(maxOrderValue : ℤ) by lia, valueOfOrderValue_neg_maxOrderValue]
    exact WithBotTop.bot_lt_coe _

theorem valueOfOrderValue_sub_one_lt {k : ℕ} {v : ℚ} (hk : k < maxOrderValue) (hv : 0 < v)
    (h : k ≠ 0 → (magnitudeUnits (k - 1) : ℚ) * 2 ^ (-1074 : ℤ) < v) :
    valueOfOrderValue (k - 1) < (v : WithBotTop ℚ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [show ((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) by norm_num,
      valueOfOrderValue_neg_natCast (by simp [maxOrderValue]), WithBotTop.coe_lt_coe,
      show (magnitudeUnits 1 : ℚ) = 1 by norm_num [magnitudeUnits]]
    linarith [show (0 : ℚ) < 2 ^ (-1074 : ℤ) by positivity]
  · rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by lia, valueOfOrderValue_natCast (by lia),
      WithBotTop.coe_lt_coe]
    exact h (by lia)

theorem lt_valueOfOrderValue_neg_add_one {k : ℕ} {v : ℚ} (hk : k < maxOrderValue) (hv : 0 < v)
    (h : k ≠ 0 → (magnitudeUnits (k - 1) : ℚ) * 2 ^ (-1074 : ℤ) < v) :
    ((-v : ℚ) : WithBotTop ℚ) < valueOfOrderValue (-(k : ℤ) + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [show -((0 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) by norm_num,
      valueOfOrderValue_natCast (by simp [maxOrderValue]), WithBotTop.coe_lt_coe,
      show (magnitudeUnits 1 : ℚ) = 1 by norm_num [magnitudeUnits]]
    linarith [show (0 : ℚ) < 2 ^ (-1074 : ℤ) by positivity]
  · rw [show -(k : ℤ) + 1 = -((k - 1 : ℕ) : ℤ) by lia, valueOfOrderValue_neg_natCast (by lia),
      WithBotTop.coe_lt_coe, neg_lt_neg_iff]
    exact h (by lia)

/-- A positive rational number `v` strictly between the values of the magnitudes `k - 1` and
`k + 1` next to the magnitude `k` of a finite double `x`, in units of `2 ^ (-1074)`, lies, with
the sign of `x`, strictly between the values of `nextDown x` and `nextUp x`. -/
theorem lt_nextUp_and_nextDown_lt {x : Double} {k : ℕ} {v : ℚ} (hf : x.isFinite = true)
    (hkx : x.expField * 2 ^ 52 + x.fracField = k) (hv : 0 < v)
    (hup : v < (magnitudeUnits (k + 1) : ℚ) * 2 ^ (-1074 : ℤ))
    (hdown : k ≠ 0 → (magnitudeUnits (k - 1) : ℚ) * 2 ^ (-1074 : ℤ) < v) :
    ((if x.signBit then -v else v : ℚ) : WithBotTop ℚ) < doubleValue (nextUp x).bits ∧
      doubleValue (nextDown x).bits < ((if x.signBit then -v else v : ℚ) : WithBotTop ℚ) := by
  have hx := isNaN_eq_false_of_isFinite hf
  obtain ⟨hi, hi'⟩ := ne_huge_of_isFinite hf
  have hk := hkx ▸ expField_mul_add_fracField_lt hf
  obtain ⟨hu1, hu2⟩ := orderValue_nextUp hx hi
  obtain ⟨hd1, hd2⟩ := orderValue_nextDown hx hi'
  rw [doubleValue_eq_valueOfOrderValue hu2, doubleValue_eq_valueOfOrderValue hd2, hu1, hd1,
    orderValue_eq x, hkx]
  cases x.signBit <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact ⟨lt_valueOfOrderValue_add_one hk hup, valueOfOrderValue_sub_one_lt hk hv hdown⟩
  · exact ⟨lt_valueOfOrderValue_neg_add_one hk hv hdown, valueOfOrderValue_neg_sub_one_lt hk hup⟩

/-! ### Finite, infinite and neighbouring doubles -/

theorem isFinite_iff_natAbs_orderValue_lt {x : Double} (hx : x.isNaN = false) :
    x.isFinite = true ↔ x.orderValue.natAbs < maxOrderValue := by
  have := fracField_lt x
  rcases expField_lt_or_of_isNaN_eq_false hx with h | h
  · simp only [isFinite, bne_iff_ne, ne_eq, show x.expField ≠ 2047 by lia, not_false_eq_true,
      true_iff, orderValue_eq, maxOrderValue]
    split <;> lia
  · simp only [isFinite, h.1, bne_self_eq_false, Bool.false_eq_true, false_iff, not_lt,
      orderValue_eq, h.2, maxOrderValue]
    split <;> lia

theorem isFinite_nextUp_of_expField_lt {x : Double} (hf : x.isFinite = true)
    (hE : x.expField < 2046) : (nextUp x).isFinite = true := by
  have hx := isNaN_eq_false_of_isFinite hf
  obtain ⟨h1, h2⟩ := orderValue_nextUp hx (ne_huge_of_isFinite hf).1
  rw [isFinite_iff_natAbs_orderValue_lt h2, h1, orderValue_eq, maxOrderValue]
  split <;> lia [fracField_lt x]

theorem isFinite_nextDown_or_doubleValue_eq_bot {x : Double} (hf : x.isFinite = true) :
    (nextDown x).isFinite = true ∨ doubleValue (nextDown x).bits = ⊥ := by
  have hx := isNaN_eq_false_of_isFinite hf
  obtain ⟨h1, h2⟩ := orderValue_nextDown hx (ne_huge_of_isFinite hf).2
  have h3 := (isFinite_iff_natAbs_orderValue_lt hx).mp hf
  have h4 := natAbs_orderValue_le h2
  rw [isFinite_iff_natAbs_orderValue_lt h2, doubleValue_eq_valueOfOrderValue h2, h1]
  rcases (show (x.orderValue - 1).natAbs < maxOrderValue ∨ x.orderValue - 1 = -maxOrderValue by
    rw [h1] at h4; lia) with h | h
  · exact .inl h
  · exact .inr (by rw [h, valueOfOrderValue_neg_maxOrderValue])

theorem isFinite_nextUp_or_doubleValue_eq_top {x : Double} (hf : x.isFinite = true) :
    (nextUp x).isFinite = true ∨ doubleValue (nextUp x).bits = ⊤ := by
  have hx := isNaN_eq_false_of_isFinite hf
  obtain ⟨h1, h2⟩ := orderValue_nextUp hx (ne_huge_of_isFinite hf).1
  have h3 := (isFinite_iff_natAbs_orderValue_lt hx).mp hf
  have h4 := natAbs_orderValue_le h2
  rw [isFinite_iff_natAbs_orderValue_lt h2, doubleValue_eq_valueOfOrderValue h2, h1]
  rcases (show (x.orderValue + 1).natAbs < maxOrderValue ∨ x.orderValue + 1 = maxOrderValue by
    rw [h1] at h4; lia) with h | h
  · exact .inl h
  · exact .inr (by rw [h, valueOfOrderValue_maxOrderValue])

theorem le_of_lt_nextUp {x y : Double} (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hi : x.bits ≠ huge.bits) (h : doubleValue y.bits < doubleValue (nextUp x).bits) :
    doubleValue y.bits ≤ doubleValue x.bits :=
  not_lt.mp fun h2 ↦ h.not_ge ((le_eq_true_iff (orderValue_nextUp hx hi).2 hy).mp
    (nextUp_le_of_lt hx hy hi ((lt_eq_true_iff hx hy).mpr h2)))

theorem le_nextDown_of_doubleValue_lt {x y : Double} (hx : x.isNaN = false)
    (hy : y.isNaN = false) (hi : x.bits ≠ huge.neg.bits)
    (h : doubleValue y.bits < doubleValue x.bits) :
    doubleValue y.bits ≤ doubleValue (nextDown x).bits :=
  (le_eq_true_iff hy (orderValue_nextDown hx hi).2).mp
    (le_nextDown_of_lt hx hy hi ((lt_eq_true_iff hy hx).mpr h))

theorem doubleValue_of_isInf {x : Double} (hi : x.isInf = true) :
    doubleValue x.bits = if x.signBit then ⊥ else ⊤ := by
  simp only [isInf, Bool.and_eq_true, beq_iff_eq] at hi
  rw [doubleValue_bits, ite_eq_left hi.1]

theorem zero_lt_of_isInf {x : Double} (hi : x.isInf = true) : zero.lt x = !x.signBit := by
  have hx : x.isNaN = false := by simp_all [isInf, isNaN]
  simp only [isInf, Bool.and_eq_true, beq_iff_eq] at hi
  simp only [lt, hx, orderValue_eq, hi.1, hi.2]
  cases x.signBit <;> decide

theorem isFinite_of_isInf_eq_false {x : Double} (hx : x.isNaN = false) (hi : x.isInf = false) :
    x.isFinite = true := by
  simp only [isNaN, isInf, isFinite, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    bne_eq_false_iff_eq, bne_iff_ne] at hx hi ⊢
  rcases hx with hx | hx <;> rcases hi with hi | hi <;> lia

theorem isNaN_huge : huge.isNaN = false := by decide

theorem isNaN_huge_neg : huge.neg.isNaN = false := by decide

theorem doubleValue_huge : doubleValue huge.bits = ⊤ := by decide

theorem doubleValue_huge_neg : doubleValue huge.neg.bits = ⊥ := by decide

/-! ### The last step of `ofRatio` and `ofDyadic` -/

theorem isNaN_assemble (neg : Bool) {M : ℕ} (q : ℤ) (hM : M < 2 ^ 53) :
    (assemble neg M q).isNaN = false := by
  obtain ⟨-, he, hf⟩ := fields_assemble neg q hM
  simp only [isNaN, he, hf]
  split_ifs <;> simp
  lia

theorem isNaN_ofSignificand (neg : Bool) {M : ℕ} (q : ℤ) (hM : M ≤ 2 ^ 53) :
    (ofSignificand neg M q).isNaN = false := by
  rcases hM.lt_or_eq with hM | rfl
  · rw [ofSignificand_of_ne q hM.ne]; exact isNaN_assemble neg q hM
  · rw [ofSignificand_two_pow]; exact isNaN_assemble neg _ (by norm_num)

theorem isFinite_ofSignificand {neg : Bool} {M : ℕ} {q : ℤ} (hM : M ≤ 2 ^ 53)
    (hq : q + 1076 < 2046) :
    (ofSignificand neg M q).isFinite = true ∧ (ofSignificand neg M q).signBit = neg ∧
      (ofSignificand neg M q).expField < 2046 := by
  rcases hM.lt_or_eq with hM | rfl
  · rw [ofSignificand_of_ne q hM.ne]
    obtain ⟨hs, he, -⟩ := fields_assemble neg q hM
    exact ⟨(isFinite_assemble_iff hM).mpr (.inr (by lia)), hs, by rw [he]; split_ifs <;> lia⟩
  · rw [ofSignificand_two_pow]
    obtain ⟨hs, he, -⟩ := fields_assemble neg (q + 1) (M := 2 ^ 52) (by norm_num)
    exact ⟨(isFinite_assemble_iff (by norm_num)).mpr (.inr (by lia)), hs,
      by rw [he]; split_ifs <;> lia⟩

/-! ### The magnitudes next to an assembled double -/

theorem magnitudeUnits_of_lt {M : ℕ} (h : M < 2 ^ 52) :
    magnitudeUnits M = M ∧ magnitudeUnits (M + 1) = M + 1 ∧ magnitudeUnits (M - 1) = M - 1 := by
  have h0 := magnitudeUnits_fields (E := 0) h
  have h1 := magnitudeUnits_fields_succ (E := 0) h
  have h2 := magnitudeUnits_fields (E := 0) (show M - 1 < 2 ^ 52 by lia)
  simp only [Nat.zero_mul, Nat.zero_add, ↓reduceIte] at h0 h1 h2
  exact ⟨h0, by rw [h1, h0]; rfl, h2⟩

theorem magnitudeUnits_normal_mul {M : ℕ} {q : ℤ} (h1 : 2 ^ 52 ≤ M) (h2 : M < 2 ^ 53)
    (hq : -1074 ≤ q) :
    (magnitudeUnits ((q + 1075).toNat * 2 ^ 52 + (M - 2 ^ 52)) : ℚ) * 2 ^ (-1074 : ℤ) =
      M * 2 ^ q := by
  rw [magnitudeUnits_mul_eq (by lia), ite_eq_right (by lia), Int.toNat_of_nonneg (by lia),
    Nat.cast_sub h1]
  push_cast; ring_nf

theorem magnitudeUnits_normal_succ_mul {M : ℕ} {q : ℤ} (h1 : 2 ^ 52 ≤ M) (h2 : M < 2 ^ 53)
    (hq : -1074 ≤ q) :
    (magnitudeUnits ((q + 1075).toNat * 2 ^ 52 + (M - 2 ^ 52) + 1) : ℚ) * 2 ^ (-1074 : ℤ) =
      (M + 1) * 2 ^ q := by
  rw [magnitudeUnits_fields_succ (by lia), Nat.cast_add, add_mul,
    magnitudeUnits_normal_mul h1 h2 hq, show max (q + 1075).toNat 1 - 1 = (q + 1074).toNat by lia,
    Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (by lia),
    ← zpow_add₀ two_ne_zero]
  ring_nf

theorem magnitudeUnits_mul_of_succ_eq {E F k : ℕ} (hF : F < 2 ^ 52)
    (hk : E * 2 ^ 52 + F + 1 = k) :
    (magnitudeUnits (E * 2 ^ 52 + F) : ℚ) * 2 ^ (-1074 : ℤ) =
      magnitudeUnits k * 2 ^ (-1074 : ℤ) - 2 ^ (((max E 1 - 1 : ℕ) : ℤ) - 1074) := by
  rw [← hk, magnitudeUnits_fields_succ hF, Nat.cast_add, add_mul, Nat.cast_pow, Nat.cast_ofNat,
    ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← sub_eq_add_neg]
  ring

/-- The value of the magnitude below that of a normal double `M 2 ^ q`: half a unit `2 ^ q` lower
at the bottom of a binade (`M = 2 ^ 52`, above the least exponent), a unit lower otherwise. -/
theorem magnitudeUnits_normal_pred_mul {M : ℕ} {q : ℤ} (h1 : 2 ^ 52 ≤ M) (h2 : M < 2 ^ 53)
    (hq : -1074 ≤ q) :
    (magnitudeUnits ((q + 1075).toNat * 2 ^ 52 + (M - 2 ^ 52) - 1) : ℚ) * 2 ^ (-1074 : ℤ) =
      M * 2 ^ q - if M = 2 ^ 52 ∧ -1074 < q then 2 ^ (q - 1) else 2 ^ q := by
  rw [← magnitudeUnits_normal_mul h1 h2 hq]
  by_cases hF : M = 2 ^ 52
  · subst hF
    by_cases hq' : -1074 < q
    · rw [show (q + 1075).toNat * 2 ^ 52 + (2 ^ 52 - 2 ^ 52) - 1 =
        ((q + 1075).toNat - 1) * 2 ^ 52 + (2 ^ 52 - 1) by lia,
        magnitudeUnits_mul_of_succ_eq (k := (q + 1075).toNat * 2 ^ 52 + (2 ^ 52 - 2 ^ 52))
          (by lia) (by lia), ite_eq_left ⟨rfl, hq'⟩]
      congr 2; lia
    · rw [show (q + 1075).toNat * 2 ^ 52 + (2 ^ 52 - 2 ^ 52) - 1 = 0 * 2 ^ 52 + (2 ^ 52 - 1) by
        lia, magnitudeUnits_mul_of_succ_eq (k := (q + 1075).toNat * 2 ^ 52 + (2 ^ 52 - 2 ^ 52))
          (by lia) (by lia), ite_eq_right (by lia)]
      congr 2; lia
  · rw [show (q + 1075).toNat * 2 ^ 52 + (M - 2 ^ 52) - 1 =
      (q + 1075).toNat * 2 ^ 52 + (M - 2 ^ 52 - 1) by lia,
      magnitudeUnits_mul_of_succ_eq (k := (q + 1075).toNat * 2 ^ 52 + (M - 2 ^ 52)) (by lia)
        (by lia), ite_eq_right (by lia)]
    congr 2; lia

/-- A subnormal or zero `x = ±M 2 ^ (-1074)` (`M < 2 ^ 52`) and a positive `v` within less than
`2 ^ (-1074)` of `M 2 ^ (-1074)`: the neighbours of `x` lie on either side of `±v`. -/
theorem lt_nextUp_and_nextDown_lt_assemble_of_lt {neg : Bool} {M : ℕ} {v : ℚ} (h : M < 2 ^ 52)
    (hv : 0 < v) (hup : v < (M + 1) * 2 ^ (-1074 : ℤ))
    (hdown : M ≠ 0 → (M - 1 : ℚ) * 2 ^ (-1074 : ℤ) < v) :
    ((if neg then -v else v : ℚ) : WithBotTop ℚ) <
        doubleValue (nextUp (assemble neg M (-1074))).bits ∧
      doubleValue (nextDown (assemble neg M (-1074))).bits <
        ((if neg then -v else v : ℚ) : WithBotTop ℚ) := by
  obtain ⟨hs, he, hfr⟩ := fields_assemble neg (-1074) (show M < 2 ^ 53 by lia)
  have hk :
      (assemble neg M (-1074)).expField * 2 ^ 52 + (assemble neg M (-1074)).fracField = M := by
    simp only [he, hfr, h, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
  obtain ⟨-, m1, m2⟩ := magnitudeUnits_of_lt h
  have := lt_nextUp_and_nextDown_lt ((isFinite_assemble_iff (by lia)).mpr (.inl h)) hk hv
    (by rw [m1, Nat.cast_add, Nat.cast_one]; exact hup)
    fun hM ↦ by rw [m2, Nat.cast_sub (by lia), Nat.cast_one]; exact hdown hM
  rwa [hs] at this

/-- A normal `x = ±M 2 ^ q` (`2 ^ 52 ≤ M < 2 ^ 53`) and a positive `v` below `(M + 1) 2 ^ q` and
above the value of the magnitude below that of `x`: the neighbours of `x` lie on either side of
`±v`. -/
theorem lt_nextUp_and_nextDown_lt_assemble_of_two_pow_le {neg : Bool} {M : ℕ} {q : ℤ} {v : ℚ}
    (h1 : 2 ^ 52 ≤ M) (h2 : M < 2 ^ 53) (hq : -1074 ≤ q) (hq' : q + 1075 < 2047) (hv : 0 < v)
    (hup : v < (M + 1) * 2 ^ q)
    (hdown : M * 2 ^ q - (if M = 2 ^ 52 ∧ -1074 < q then 2 ^ (q - 1) else 2 ^ q) < v) :
    ((if neg then -v else v : ℚ) : WithBotTop ℚ) < doubleValue (nextUp (assemble neg M q)).bits ∧
      doubleValue (nextDown (assemble neg M q)).bits <
        ((if neg then -v else v : ℚ) : WithBotTop ℚ) := by
  obtain ⟨hs, he, hfr⟩ := fields_assemble neg q h2
  have hk : (assemble neg M q).expField * 2 ^ 52 + (assemble neg M q).fracField =
      (q + 1075).toNat * 2 ^ 52 + (M - 2 ^ 52) := by
    simp only [he, hfr, show ¬M < 2 ^ 52 by lia, show ¬2047 ≤ q + 1075 by lia, ↓reduceIte]
  have := lt_nextUp_and_nextDown_lt ((isFinite_assemble_iff h2).mpr (.inr hq')) hk hv
    (by rwa [magnitudeUnits_normal_succ_mul h1 h2 hq])
    fun _ ↦ by rwa [magnitudeUnits_normal_pred_mul h1 h2 hq]
  rwa [hs] at this

/-! ### Faithful rounding of a significand -/

theorem lt_nextUp_and_nextDown_lt_ofSignificand_two_pow {neg : Bool} {q : ℤ} {v : ℚ}
    (hv : 0 < v) (hq : -1074 ≤ q) (hlo : (2 ^ 53 : ℕ) * 2 ^ q - 2 ^ (q - 1) ≤ v)
    (hhi : v ≤ (2 ^ 53 : ℕ) * 2 ^ q + 2 ^ (q - 1))
    (hf : (ofSignificand neg (2 ^ 53) q).isFinite = true) :
    ((if neg then -v else v : ℚ) : WithBotTop ℚ) <
        doubleValue (nextUp (ofSignificand neg (2 ^ 53) q)).bits ∧
      doubleValue (nextDown (ofSignificand neg (2 ^ 53) q)).bits <
        ((if neg then -v else v : ℚ) : WithBotTop ℚ) := by
  rw [ofSignificand_two_pow] at hf ⊢
  have hq' : q + 1 + 1075 < 2047 :=
    ((isFinite_assemble_iff (by norm_num)).mp hf).resolve_left (lt_irrefl _)
  have ht : (0 : ℚ) < 2 ^ q := by positivity
  rw [zpow_sub_one₀ two_ne_zero] at hlo hhi
  push_cast at hlo hhi
  refine lt_nextUp_and_nextDown_lt_assemble_of_two_pow_le le_rfl (by norm_num) (by lia) hq' hv
    ?_ ?_
  · rw [zpow_add_one₀ two_ne_zero]; push_cast; linarith
  · rw [ite_eq_left ⟨rfl, by lia⟩, add_sub_cancel_right, zpow_add_one₀ two_ne_zero]
    push_cast; linarith

-- A significand `M < 2 ^ 52` with `v ≤ M 2 ^ q + 2 ^ (q - 1)`, where `2 ^ (q + 52) ≤ v` unless
-- `q = -1074`, comes only with the least exponent `q = -1074`.
private theorem eq_of_lt_of_two_zpow_le {M : ℕ} {q : ℤ} {v : ℚ} (h : M < 2 ^ 52)
    (hhi : v ≤ M * 2 ^ q + 2 ^ (q - 1)) (hnorm : -1074 < q → 2 ^ (q + 52) ≤ v)
    (hq : -1074 ≤ q) : q = -1074 := by
  by_contra hq'
  have h1 := hnorm (by lia)
  have h2 : (M : ℚ) + 1 ≤ 2 ^ 52 := mod_cast (by lia : M + 1 ≤ 2 ^ 52)
  have ht : (0 : ℚ) < 2 ^ q := by positivity
  rw [zpow_sub_one₀ two_ne_zero] at hhi
  rw [zpow_add₀ two_ne_zero, zpow_ofNat] at h1
  have := mul_le_mul_of_nonneg_right h2 ht.le
  linarith

theorem lt_nextUp_and_nextDown_lt_ofSignificand_of_ne {neg : Bool} {M : ℕ} {q : ℤ} {v : ℚ}
    (hv : 0 < v) (hM : M < 2 ^ 53) (hq : -1074 ≤ q) (hlo : M * 2 ^ q - 2 ^ (q - 1) ≤ v)
    (hhi : v ≤ M * 2 ^ q + 2 ^ (q - 1)) (hnorm : -1074 < q → 2 ^ (q + 52) ≤ v)
    (hf : (ofSignificand neg M q).isFinite = true) :
    ((if neg then -v else v : ℚ) : WithBotTop ℚ) <
        doubleValue (nextUp (ofSignificand neg M q)).bits ∧
      doubleValue (nextDown (ofSignificand neg M q)).bits <
        ((if neg then -v else v : ℚ) : WithBotTop ℚ) := by
  rw [ofSignificand_of_ne q hM.ne] at hf ⊢
  by_cases hs : M < 2 ^ 52
  · obtain rfl := eq_of_lt_of_two_zpow_le hs hhi hnorm hq
    rw [zpow_sub_one₀ two_ne_zero] at hlo hhi
    have ht : (0 : ℚ) < 2 ^ (-1074 : ℤ) := by positivity
    exact lt_nextUp_and_nextDown_lt_assemble_of_lt hs hv (by linarith) fun _ ↦ by linarith
  have hq' : q + 1075 < 2047 := ((isFinite_assemble_iff hM).mp hf).resolve_left hs
  have ht : (0 : ℚ) < 2 ^ (q - 1) := by positivity
  refine lt_nextUp_and_nextDown_lt_assemble_of_two_pow_le (by lia) hM hq hq' hv ?_ ?_
  · rw [zpow_sub_one₀ two_ne_zero] at hhi ht; linarith
  · split_ifs with hc
    · have h := hnorm hc.2
      rw [zpow_add₀ two_ne_zero, zpow_ofNat] at h
      rw [hc.1]; push_cast; linarith
    · rw [zpow_sub_one₀ two_ne_zero] at hlo ht; linarith

/-- The double of a significand `M ≤ 2 ^ 53` rounded from a positive `v` to within half a unit of
the exponent `q ≥ -1074` of its last place, with `v ≥ 2 ^ (q + 52)` when `q` is not the least
exponent, is a faithful rounding of `±v` when it is finite. -/
theorem lt_nextUp_and_nextDown_lt_ofSignificand {neg : Bool} {M : ℕ} {q : ℤ} {v : ℚ}
    (hv : 0 < v) (hM : M ≤ 2 ^ 53) (hq : -1074 ≤ q) (hlo : M * 2 ^ q - 2 ^ (q - 1) ≤ v)
    (hhi : v ≤ M * 2 ^ q + 2 ^ (q - 1)) (hnorm : -1074 < q → 2 ^ (q + 52) ≤ v)
    (hf : (ofSignificand neg M q).isFinite = true) :
    ((if neg then -v else v : ℚ) : WithBotTop ℚ) <
        doubleValue (nextUp (ofSignificand neg M q)).bits ∧
      doubleValue (nextDown (ofSignificand neg M q)).bits <
        ((if neg then -v else v : ℚ) : WithBotTop ℚ) := by
  rcases hM.lt_or_eq with hM | rfl
  · exact lt_nextUp_and_nextDown_lt_ofSignificand_of_ne hv hM hq hlo hhi hnorm hf
  · exact lt_nextUp_and_nextDown_lt_ofSignificand_two_pow hv hq hlo hhi hf

/-! ### Rounding to the nearest integer -/

/-- `a / b` rounded to the nearest integer, ties to even, as `Ratpoints.Double.ofRatio` rounds
the quotient of `a` and `b ≠ 0`: the remainder `r` decides, rounding up when `2 r > b` and when
`2 r = b` and the quotient is odd. -/
def roundDiv (a b : ℕ) : ℕ :=
  if b < 2 * (a % b) ∨ 2 * (a % b) = b ∧ (a / b) % 2 = 1 then a / b + 1 else a / b

theorem roundDiv_bounds_nat (a : ℕ) {b : ℕ} (hb : 0 < b) :
    2 * roundDiv a b * b ≤ 2 * a + b ∧ 2 * a ≤ (2 * roundDiv a b + 1) * b := by
  have h := Nat.div_add_mod a b
  have hr := Nat.mod_lt a hb
  simp only [roundDiv]
  split_ifs <;> exact ⟨by lia, by lia⟩

theorem roundDiv_bounds (a : ℕ) {b : ℕ} (hb : 0 < b) :
    (roundDiv a b : ℚ) - 1 / 2 ≤ a / b ∧ (a : ℚ) / b ≤ roundDiv a b + 1 / 2 := by
  obtain ⟨h1, h2⟩ := roundDiv_bounds_nat a hb
  have hb' : (0 : ℚ) < b := mod_cast hb
  have h1' : (2 * roundDiv a b * b : ℚ) ≤ 2 * a + b := mod_cast h1
  have h2' : (2 * a : ℚ) ≤ (2 * roundDiv a b + 1) * b := mod_cast h2
  exact ⟨by rw [le_div_iff₀ hb']; linarith, by rw [div_le_iff₀ hb']; linarith⟩

theorem roundShift_eq_roundDiv (m : ℕ) {k : ℤ} (hk : 0 < k) :
    roundShift m k = roundDiv m (2 ^ k.toNat) := by
  simp only [roundShift, show ¬k ≤ 0 by lia, ↓reduceIte, Nat.shiftRight_eq_div_pow, roundDiv]
  split_ifs <;> lia [Nat.two_pow_pred_mul_two (show 0 < k.toNat by lia)]

theorem roundShift_bounds (m : ℕ) (k : ℤ) :
    (roundShift m k : ℚ) - 1 / 2 ≤ m / 2 ^ k ∧ (m : ℚ) / 2 ^ k ≤ roundShift m k + 1 / 2 := by
  rcases le_or_gt k 0 with hk | hk
  · rw [roundShift_of_nonpos hk]
    have : (m : ℚ) / 2 ^ k = ((m * 2 ^ (-k).toNat : ℕ) : ℚ) := by
      push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg (by lia), zpow_neg, div_eq_mul_inv]
    rw [this]; constructor <;> linarith
  · rw [roundShift_eq_roundDiv m hk]
    have := roundDiv_bounds m (Nat.two_pow_pos k.toNat)
    rwa [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg hk.le] at this

-- From the rounding `M - 1/2 ≤ v / 2 ^ q ≤ M + 1/2` of a number `v < 2 ^ (q + 53)`, the bounds
-- that `Ratpoints.Double.lt_nextUp_and_nextDown_lt_ofSignificand` takes but for the exponent.
private theorem round_bounds {M : ℕ} {q : ℤ} {v : ℚ} (h1 : (M : ℚ) - 1 / 2 ≤ v / 2 ^ q)
    (h2 : v / 2 ^ q ≤ M + 1 / 2) (hv : v < 2 ^ (q + 53)) :
    M ≤ 2 ^ 53 ∧ M * 2 ^ q - 2 ^ (q - 1) ≤ v ∧ v ≤ M * 2 ^ q + 2 ^ (q - 1) := by
  have ht : (0 : ℚ) < 2 ^ q := by positivity
  rw [le_div_iff₀ ht] at h1
  rw [div_le_iff₀ ht] at h2
  rw [zpow_add₀ two_ne_zero, zpow_ofNat] at hv
  have h3 : ((M : ℚ) - 1 / 2) * 2 ^ q < 2 ^ 53 * 2 ^ q := by linarith
  have h4 : M < 2 ^ 53 + 1 := by
    have := lt_of_mul_lt_mul_right h3 ht.le
    exact_mod_cast (show (M : ℚ) < 2 ^ 53 + 1 by linarith)
  rw [zpow_sub_one₀ two_ne_zero]
  exact ⟨by lia, by linarith, by linarith⟩

/-! ### `ofRatio` -/

/-- The exponent `E` with `2 ^ E ≤ n / d < 2 ^ (E + 1)` that `Ratpoints.Double.ofRatio` finds
from the lengths of `n` and `d` in bits and one comparison
(`Ratpoints.Double.ratioExponent_bounds`). -/
def ratioExponent (n d : ℕ) : ℤ :=
  let e : ℤ := (n.log2 : ℤ) - d.log2
  let atLeast : Bool := if 0 ≤ e then d * 2 ^ e.toNat ≤ n else d ≤ n * 2 ^ (-e).toNat
  if atLeast then e else e - 1

/-- The exponent of the last place of the double that `Ratpoints.Double.ofRatio` rounds `n / d`
to: `Ratpoints.Double.ratioExponent n d - 52`, and `-1074` for the subnormals. -/
def ratioLast (n d : ℕ) : ℤ := max (ratioExponent n d - 52) (-1074)

/-- The numerator and the denominator of `n / (d 2 ^ q)` that `Ratpoints.Double.ofRatio`
divides. -/
def ratioPair (n d : ℕ) (q : ℤ) : ℕ × ℕ :=
  if 0 ≤ q then (n, d * 2 ^ q.toNat) else (n * 2 ^ (-q).toNat, d)

theorem ofRatio_eq {neg : Bool} {n : ℕ} (d : ℕ) (hn : n ≠ 0) :
    ofRatio neg n d = ofSignificand neg
      (roundDiv (ratioPair n d (ratioLast n d)).1 (ratioPair n d (ratioLast n d)).2)
        (ratioLast n d) := by
  rw [ofRatio, ite_eq_right hn]
  rfl

theorem two_zpow_le_div_iff {n d : ℕ} (hd : d ≠ 0) (e : ℤ) :
    (if 0 ≤ e then decide (d * 2 ^ e.toNat ≤ n) else decide (d ≤ n * 2 ^ (-e).toNat)) = true ↔
      (2 : ℚ) ^ e ≤ n / d := by
  have hd' : (0 : ℚ) < d := mod_cast Nat.pos_of_ne_zero hd
  rw [le_div_iff₀ hd']
  split_ifs with he
  · rw [decide_eq_true_iff, ← Int.toNat_of_nonneg he, zpow_natCast, mul_comm]
    exact_mod_cast Iff.rfl
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = -(k : ℤ) := ⟨(-e).toNat, by lia⟩
    rw [decide_eq_true_iff, neg_neg, Int.toNat_natCast, zpow_neg, zpow_natCast,
      ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    exact_mod_cast Iff.rfl

theorem two_zpow_log2_div_bounds {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) :
    (2 : ℚ) ^ ((n.log2 : ℤ) - d.log2 - 1) < n / d ∧
      (n : ℚ) / d < 2 ^ ((n.log2 : ℤ) - d.log2 + 1) := by
  have h1 : (2 : ℚ) ^ n.log2 ≤ n := mod_cast Nat.log2_self_le hn
  have h2 : (n : ℚ) < 2 ^ (n.log2 + 1) := mod_cast Nat.lt_log2_self
  have h3 : (2 : ℚ) ^ d.log2 ≤ d := mod_cast Nat.log2_self_le hd
  have h4 : (d : ℚ) < 2 ^ (d.log2 + 1) := mod_cast Nat.lt_log2_self
  have hd' : (0 : ℚ) < d := mod_cast Nat.pos_of_ne_zero hd
  constructor
  · rw [lt_div_iff₀ hd', show (n.log2 : ℤ) - d.log2 - 1 = n.log2 - (d.log2 + 1 : ℕ) by
      push_cast; ring, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, div_mul_eq_mul_div,
      div_lt_iff₀ (by positivity)]
    exact mul_lt_mul' h1 h4 hd'.le (by have := Nat.pos_of_ne_zero hn; positivity)
  · rw [div_lt_iff₀ hd', show (n.log2 : ℤ) - d.log2 + 1 = (n.log2 + 1 : ℕ) - d.log2 by
      push_cast; ring, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, div_mul_eq_mul_div,
      lt_div_iff₀ (by positivity)]
    exact mul_lt_mul h2 h3 (by positivity) (by positivity)

theorem ratioExponent_bounds {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) :
    (2 : ℚ) ^ ratioExponent n d ≤ n / d ∧ (n : ℚ) / d < 2 ^ (ratioExponent n d + 1) := by
  obtain ⟨h1, h2⟩ := two_zpow_log2_div_bounds hn hd
  simp only [ratioExponent, two_zpow_le_div_iff hd]
  split_ifs with h
  · exact ⟨h, h2⟩
  · rw [sub_add_cancel]
    exact ⟨h1.le, not_le.mp h⟩

theorem ratioPair_snd_pos {n d : ℕ} (hd : d ≠ 0) (q : ℤ) : 0 < (ratioPair n d q).2 := by
  simp only [ratioPair]
  split_ifs <;> positivity

theorem ratioPair_div (n d : ℕ) (q : ℤ) :
    ((ratioPair n d q).1 : ℚ) / (ratioPair n d q).2 = n / d / 2 ^ q := by
  simp only [ratioPair]
  split_ifs with hq
  · push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg hq, div_div]
  · push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by lia), zpow_neg]
    ring

/-- The significand `M` and the exponent `q` of its last place that `Ratpoints.Double.ofRatio`
rounds `n / d` to: `M ≤ 2 ^ 53`, `q ≥ -1074`, `M 2 ^ q` within half a unit `2 ^ (q - 1)` of
`n / d`, and `n / d ≥ 2 ^ (q + 52)` when `q` is not the least exponent. -/
theorem ofRatio_rounding {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) :
    roundDiv (ratioPair n d (ratioLast n d)).1 (ratioPair n d (ratioLast n d)).2 ≤ 2 ^ 53 ∧
      -1074 ≤ ratioLast n d ∧
      (roundDiv (ratioPair n d (ratioLast n d)).1 (ratioPair n d (ratioLast n d)).2 : ℚ) *
          2 ^ ratioLast n d - 2 ^ (ratioLast n d - 1) ≤ n / d ∧
      (n : ℚ) / d ≤ (roundDiv (ratioPair n d (ratioLast n d)).1
          (ratioPair n d (ratioLast n d)).2 : ℚ) * 2 ^ ratioLast n d + 2 ^ (ratioLast n d - 1) ∧
      (-1074 < ratioLast n d → 2 ^ (ratioLast n d + 52) ≤ (n : ℚ) / d) := by
  obtain ⟨h1, h2⟩ := roundDiv_bounds (ratioPair n d (ratioLast n d)).1 (ratioPair_snd_pos hd _)
  obtain ⟨e1, e2⟩ := ratioExponent_bounds hn hd
  rw [ratioPair_div] at h1 h2
  have hq1 := le_max_left (ratioExponent n d - 52) (-1074)
  obtain ⟨hM, hlo, hhi⟩ := round_bounds h1 h2
    (e2.trans_le (zpow_le_zpow_right₀ one_le_two (by rw [ratioLast]; lia)))
  refine ⟨hM, le_max_right _ _, hlo, hhi, fun hq ↦ ?_⟩
  rw [ratioLast, max_eq_left (by rw [ratioLast] at hq; lia), sub_add_cancel]; exact e1

/-- `Ratpoints.Double.ofRatio` rounds faithfully: when it is finite, `±n / d` lies strictly
between the neighbours of the result. -/
theorem lt_nextUp_and_nextDown_lt_ofRatio {neg : Bool} {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0)
    (hf : (ofRatio neg n d).isFinite = true) :
    ((if neg then -((n : ℚ) / d) else (n : ℚ) / d : ℚ) : WithBotTop ℚ) <
        doubleValue (nextUp (ofRatio neg n d)).bits ∧
      doubleValue (nextDown (ofRatio neg n d)).bits <
        ((if neg then -((n : ℚ) / d) else (n : ℚ) / d : ℚ) : WithBotTop ℚ) := by
  obtain ⟨hM, hq, hlo, hhi, hnorm⟩ := ofRatio_rounding hn hd
  rw [ofRatio_eq d hn] at hf ⊢
  exact lt_nextUp_and_nextDown_lt_ofSignificand (by positivity) hM hq hlo hhi hnorm hf

theorem isNaN_ofRatio (neg : Bool) (n : ℕ) {d : ℕ} (hd : d ≠ 0) :
    (ofRatio neg n d).isNaN = false := by
  by_cases hn : n = 0
  · subst hn; cases neg <;> simp [ofRatio, isNaN, expField, fracField]
  · rw [ofRatio_eq d hn]; exact isNaN_ofSignificand neg _ (ofRatio_rounding hn hd).1

/-! ### `ofDyadic` -/

theorem ofDyadic_eq {neg : Bool} {m : ℕ} (e : ℤ) (hm : m ≠ 0) :
    ofDyadic neg m e = ofSignificand neg (roundShift m (max ((m.log2 : ℤ) + e - 52) (-1074) - e))
      (max ((m.log2 : ℤ) + e - 52) (-1074)) := by
  rw [ofDyadic, ite_eq_right hm]

/-- The significand `M` and the exponent `q` of its last place that `Ratpoints.Double.ofDyadic`
rounds `m 2 ^ e` to: `M ≤ 2 ^ 53`, `q ≥ -1074`, `M 2 ^ q` within half a unit `2 ^ (q - 1)` of
`m 2 ^ e`, and `m 2 ^ e ≥ 2 ^ (q + 52)` when `q` is not the least exponent. -/
theorem ofDyadic_rounding {m : ℕ} (hm : m ≠ 0) (e : ℤ) :
    roundShift m (max ((m.log2 : ℤ) + e - 52) (-1074) - e) ≤ 2 ^ 53 ∧
      -1074 ≤ max ((m.log2 : ℤ) + e - 52) (-1074) ∧
      (roundShift m (max ((m.log2 : ℤ) + e - 52) (-1074) - e) : ℚ) *
          2 ^ max ((m.log2 : ℤ) + e - 52) (-1074) -
        2 ^ (max ((m.log2 : ℤ) + e - 52) (-1074) - 1) ≤ m * 2 ^ e ∧
      (m : ℚ) * 2 ^ e ≤ (roundShift m (max ((m.log2 : ℤ) + e - 52) (-1074) - e) : ℚ) *
          2 ^ max ((m.log2 : ℤ) + e - 52) (-1074) +
        2 ^ (max ((m.log2 : ℤ) + e - 52) (-1074) - 1) ∧
      (-1074 < max ((m.log2 : ℤ) + e - 52) (-1074) →
        2 ^ (max ((m.log2 : ℤ) + e - 52) (-1074) + 52) ≤ (m : ℚ) * 2 ^ e) := by
  have hq1 := le_max_left ((m.log2 : ℤ) + e - 52) (-1074)
  obtain ⟨h1, h2⟩ := roundShift_bounds m (max ((m.log2 : ℤ) + e - 52) (-1074) - e)
  obtain ⟨e1, e2⟩ := two_zpow_log2_le_mul hm e
  rw [zpow_sub₀ two_ne_zero, div_div_eq_mul_div] at h1 h2
  obtain ⟨hM, hlo, hhi⟩ := round_bounds h1 h2
    (e2.trans_le (zpow_le_zpow_right₀ one_le_two (by lia)))
  refine ⟨hM, le_max_right _ _, hlo, hhi, fun hq ↦ ?_⟩
  rw [max_eq_left (by lia), sub_add_cancel]
  exact e1

/-- `Ratpoints.Double.ofDyadic` rounds faithfully: when it is finite, `±m 2 ^ e` lies strictly
between the neighbours of the result. -/
theorem lt_nextUp_and_nextDown_lt_ofDyadic {neg : Bool} {m : ℕ} {e : ℤ} (hm : m ≠ 0)
    (hf : (ofDyadic neg m e).isFinite = true) :
    ((if neg then -((m : ℚ) * 2 ^ e) else (m : ℚ) * 2 ^ e : ℚ) : WithBotTop ℚ) <
        doubleValue (nextUp (ofDyadic neg m e)).bits ∧
      doubleValue (nextDown (ofDyadic neg m e)).bits <
        ((if neg then -((m : ℚ) * 2 ^ e) else (m : ℚ) * 2 ^ e : ℚ) : WithBotTop ℚ) := by
  obtain ⟨hM, hq, hlo, hhi, hnorm⟩ := ofDyadic_rounding hm e
  rw [ofDyadic_eq e hm] at hf ⊢
  exact lt_nextUp_and_nextDown_lt_ofSignificand (by positivity) hM hq hlo hhi hnorm hf

theorem isNaN_ofDyadic (neg : Bool) (m : ℕ) (e : ℤ) : (ofDyadic neg m e).isNaN = false := by
  by_cases hm : m = 0
  · subst hm; cases neg <;> simp [ofDyadic, isNaN, expField, fracField]
  · rw [ofDyadic_eq e hm]; exact isNaN_ofSignificand neg _ (ofDyadic_rounding hm e).1

/-! ### The double of the height bound -/

/-- The double of `1 ≤ H < 2 ^ 63` is finite, with the sign bit clear, and the next double is finite
and above `H`. -/
theorem isFinite_ofInt64_and_lt_toRat_nextUp {H : ℕ} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) :
    (ofInt64 H.toInt64).isFinite = true ∧ (ofInt64 H.toInt64).signBit = false ∧
      (nextUp (ofInt64 H.toInt64)).isFinite = true ∧
      (H : ℚ) < (nextUp (ofInt64 H.toInt64)).toRat := by
  have hH' : H.toInt64.toInt = H := Int64.toInt_ofNat_of_lt hH63
  have hm : H ≠ 0 := by lia
  have hl : H.log2 < 63 := (Nat.log2_lt hm).mpr hH63
  rw [ofInt64, hH', show decide (H.toInt64 < 0) = false by simp [Int64.lt_iff_toInt_lt, hH'],
    Int.natAbs_natCast]
  obtain ⟨hf, hs, hE⟩ : (ofDyadic false H 0).isFinite = true ∧
      (ofDyadic false H 0).signBit = false ∧ (ofDyadic false H 0).expField < 2046 := by
    rw [ofDyadic_eq 0 hm]
    exact isFinite_ofSignificand (ofDyadic_rounding hm 0).1 (by lia)
  have hf' := isFinite_nextUp_of_expField_lt hf hE
  refine ⟨hf, hs, hf', ?_⟩
  have h := (lt_nextUp_and_nextDown_lt_ofDyadic (neg := false) hm hf).1
  rw [doubleValue_eq_toRat hf', WithBotTop.coe_lt_coe] at h
  simpa using h

/-- The double of `1 ≤ H < 2 ^ 63`, moved up to the next double when it is below `2 ^ 63` and its
conversion to a `long` is below `H`, is finite and at least `H`: the bound `h` of the default
search interval `[-h, h]` of `Ratpoints.searchIntervals`, and `Ratpoints.Cli.heightEnd`. -/
theorem isFinite_and_le_toRat_ofInt64_nextUp {H : ℕ} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) :
    let h := ofInt64 H.toInt64
    let h := if h.lt .twoPow63 && decide (h.toInt64 < H.toInt64) then h.nextUp else h
    h.isFinite = true ∧ (H : ℚ) ≤ h.toRat := by
  intro h0 h
  obtain ⟨hf, hs, hf', hv⟩ := isFinite_ofInt64_and_lt_toRat_nextUp hH hH63
  have hlt := lt_twoPow63_eq_true_iff_toRat hf
  by_cases h1 : h0.lt .twoPow63 = true
  · by_cases h2 : h0.toInt64 < H.toInt64
    · simp only [h, h1, h2, decide_true, Bool.and_self, ↓reduceIte]
      exact ⟨hf', hv.le⟩
    · simp only [h, h1, h2, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hf, le_toRat_of_not_toInt64_lt (toRat_nonneg hs) (hlt.mp h1) hH63 h2⟩
  · simp only [h, h1, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have : (2 : ℚ) ^ 63 ≤ h0.toRat := not_lt.mp (mt hlt.mpr h1)
    have : (H : ℚ) < 2 ^ 63 := mod_cast hH63
    exact ⟨hf, by linarith⟩

/-! ### Zeros and infinities -/

theorem beq_zero_ofRatio_zero (neg : Bool) (d : ℕ) : (ofRatio neg 0 d).beq .zero = true := by
  rw [ofRatio, ite_eq_left rfl]; cases neg <;> decide

theorem isFinite_ite_huge (neg : Bool) :
    (if neg then Double.huge.neg else Double.huge).isFinite = false := by
  cases neg <;> decide

theorem nextUp_of_beq_zero {x : Double} (hz : x.beq .zero = true) : nextUp x = ⟨1⟩ := by
  simp only [Double.beq, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hz
  obtain ⟨⟨hx, -⟩, ho⟩ := hz
  have h0 : x.bits.toNat % 2 ^ 63 = 0 := by
    rw [orderValue_eq_mod, show Double.zero.orderValue = 0 by decide] at ho
    split at ho <;> lia
  have hi : x.bits ≠ huge.bits := fun h ↦ by rw [h, toNat_huge] at h0; simp [maxOrderValue] at h0
  simp [nextUp, hx, hi, isZero_eq_decide, show x.bits.toNat % 9223372036854775808 = 0 from h0]

theorem toRat_zero_nextUp : Double.zero.nextUp.toRat = 2 ^ (-1074 : ℤ) := by
  rw [nextUp_of_beq_zero (by decide)]
  obtain ⟨-, -, hr⟩ := toRat_of_toNat_eq (x := ⟨1⟩) (neg := false) (E := 0) (F := 1) (by decide)
    (by decide) rfl
  rw [hr]; simp

theorem doubleValue_one :
    doubleValue (1 : UInt64) = (((2 : ℚ) ^ (-1074 : ℤ) : ℚ) : WithBotTop ℚ) := by
  decide +kernel

end Double

end Ratpoints

end
