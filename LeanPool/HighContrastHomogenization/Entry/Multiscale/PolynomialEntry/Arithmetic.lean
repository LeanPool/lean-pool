/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# High-contrast homogenization: Entry.Multiscale.PolynomialEntry.Arithmetic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Arithmetic of the polynomial entry scales

This module proves the elementary numeric estimates that dominate the linear window scales of
the polynomial entry by the exponential scale `3 ^ d` and convert them into the logarithmic
coefficient of `t.polynomial.entry`.

It establishes the growth bound `2 * d ≤ 3 ^ d` together with its monotone form, the
positivity and monotonicity of the base-three logarithms `log₃ 2`, `log₃ (2 + x)` and
`log₃ (2 * K)`, and the resulting real and integer bounds on the entry scale `j_*`, on the
entry constant `C` assembled from the fixed constants and `(3 + d) / log₃ 2`, and on the
terminal scale.  These are the estimates that fix the threshold and the logarithmic
coefficient `c = log₃ (2 + Π K)` appearing in `t.polynomial.entry`.
-/

namespace HCPolySupport.HighContrast.Multiscale

/-- For every natural number `d`, twice `d` is at most `3` to the power `d`. This is the
elementary growth bound used to dominate the linear scales occurring in `t.polynomial.entry`
by the exponential scale `3 ^ d`. -/
theorem two_mul_le_three_pow (d : ℕ) : 2 * d ≤ 3 ^ d := by
  induction d with
  | zero => decide
  | succ d ih =>
    cases d with
    | zero => decide
    | succ d =>
      simp only [Nat.pow_succ] at ih ⊢
      omega

/-- Monotonicity form of `two_mul_le_three_pow`: if `d ≤ j`, then `2 * d ≤ 3 ^ j`. -/
theorem two_mul_le_three_pow_of_le (d j : ℕ) (h : d ≤ j) : 2 * d ≤ 3 ^ j :=
  (Nat.mul_le_mul_left 2 h).trans (two_mul_le_three_pow j)

/-- The base-three logarithm of `2` is positive, so `log₃ 2` is a legitimate positive
normalising factor for the entry scales of `t.polynomial.entry`. -/
theorem zero_lt_logb_three_two : 0 < Real.logb 3 2 :=
  Real.logb_pos (by norm_num) (by norm_num)

/-- For `x ≥ 0` the base-three logarithm of `2 + x` is nonnegative. -/
theorem logb_two_add_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Real.logb 3 (2 + x) := by
  apply Real.logb_nonneg (by norm_num)
  linarith only [hx]

/-- For `K ≥ 1` the base-three logarithm of `2 * K` is nonnegative. -/
theorem logb_two_mul_nonneg_of_one_le (K : ℝ) (hK : 1 ≤ K) :
    0 ≤ Real.logb 3 (2 * K) := by
  apply Real.logb_nonneg (by norm_num)
  linarith only [hK]

/-- Adding a nonnegative quantity inside the argument of the base-three logarithm does not
decrease its value below `log₃ 2`. -/
theorem logb_two_le_logb_two_add (x : ℝ) (hx : 0 ≤ x) :
    Real.logb 3 2 ≤ Real.logb 3 (2 + x) := by
  apply Real.logb_le_logb_of_le (by norm_num) (by norm_num)
  linarith only [hx]

/-- For `x ≥ 0` and `K ≥ 1`, replacing `x` by `x * K` in `2 + x` only increases the
base-three logarithm; this is the monotonicity used when the source term is multiplied by
the ellipticity constant `K`. -/
theorem logb_two_add_le_logb_two_add_mul (x K : ℝ) (hx : 0 ≤ x) (hK : 1 ≤ K) :
    Real.logb 3 (2 + x) ≤ Real.logb 3 (2 + x * K) := by
  apply Real.logb_le_logb_of_le (by norm_num) (by linarith only [hx])
  nlinarith only [hx, hK, mul_nonneg hx (sub_nonneg.mpr hK)]

/-- For `x ≥ 1` and `K ≥ 1`, the logarithm of `2 * K` is dominated by twice the logarithm of
`2 + x * K`; this turns the entry constant into a coefficient of the logarithmic scale
`c = log₃ (2 + Π K)` in `t.polynomial.entry`. -/
theorem logb_two_mul_le_two_mul_logb (x K : ℝ) (hx : 1 ≤ x) (hK : 1 ≤ K) :
    Real.logb 3 (2 * K) ≤ 2 * Real.logb 3 (2 + x * K) := by
  have hKx : K ≤ x * K := by nlinarith only [hx, hK]
  have ht : 0 ≤ x * K := mul_nonneg (by linarith only [hx]) (by linarith only [hK])
  have hsq : 2 * K ≤ (2 + x * K) ^ 2 := by
    nlinarith only [hKx, ht, sq_nonneg (x * K)]
  have hlog : Real.logb 3 (2 * K) ≤ Real.logb 3 ((2 + x * K) ^ 2) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith only [hK]) hsq
  rw [Real.logb_pow] at hlog
  exact hlog

/-- For `M ≥ 0` and `c ≥ log₃ 2`, the quantity `M / log₃ 2 * c` dominates `M`; this is the
normalisation step that lets the linear term `3 + d` be paid for by the logarithmic
coefficient `c` in `t.polynomial.entry`. -/
theorem le_div_logb_mul (M c : ℝ) (hM : 0 ≤ M) (hc : Real.logb 3 2 ≤ c) :
    M ≤ M / Real.logb 3 2 * c := by
  have hL : 0 < Real.logb 3 2 := zero_lt_logb_three_two
  calc M = M / Real.logb 3 2 * Real.logb 3 2 := by
        rw [div_mul_cancel₀ M hL.ne']
    _ ≤ M / Real.logb 3 2 * c := mul_le_mul_of_nonneg_left hc (div_nonneg hM hL.le)

/-- The entry scale `j_*` of `t.polynomial.entry`: the integer ceiling of `A * a + Csrc * b`,
shifted up by `d`. -/
@[expose]
noncomputable def entryScale (A Csrc a b : ℝ) (d : ℕ) : ℕ := ⌈A * a + Csrc * b⌉.toNat + d

/-- The entry scale is at least its prescribed shift `d`. -/
theorem le_entryScale (A Csrc a b : ℝ) (d : ℕ) : d ≤ entryScale A Csrc a b d := by
  unfold entryScale
  exact Nat.le_add_left d _

/-- If `Csrc' ≤ Csrc` and `b ≥ 0`, then the integer ceiling computed with `Csrc'` is still
dominated by the entry scale computed with `Csrc`. -/
theorem ceil_le_entryScale (A Csrc Csrc' a b : ℝ) (d : ℕ) (hb : 0 ≤ b) (hC : Csrc' ≤ Csrc) :
    ⌈A * a + Csrc' * b⌉ ≤ (entryScale A Csrc a b d : ℤ) := by
  unfold entryScale
  push_cast
  have hle : A * a + Csrc' * b ≤ A * a + Csrc * b := by
    linarith only [mul_le_mul_of_nonneg_right hC hb]
  have h1 : ⌈A * a + Csrc' * b⌉ ≤ ⌈A * a + Csrc * b⌉ := Int.ceil_le_ceil hle
  have h2 : ⌈A * a + Csrc * b⌉ ≤ (⌈A * a + Csrc * b⌉.toNat : ℤ) :=
    Int.self_le_toNat _
  exact h1.trans (h2.trans (le_add_of_nonneg_right (Int.natCast_nonneg d)))

/-- The entry scale, viewed in `ℝ`, is at most its real defining expression plus one and the
shift `d`, whenever that expression is nonnegative. -/
theorem entryScale_le (A Csrc a b : ℝ) (d : ℕ) (h : 0 ≤ A * a + Csrc * b) :
    (entryScale A Csrc a b d : ℝ) ≤ A * a + Csrc * b + 1 + d := by
  unfold entryScale
  push_cast
  have hceil_nn : 0 ≤ ⌈A * a + Csrc * b⌉ := Int.ceil_nonneg h
  have htoNat : ((⌈A * a + Csrc * b⌉.toNat : ℝ)) = (⌈A * a + Csrc * b⌉ : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hceil_nn)
  rw [htoNat]
  have hlt : (⌈A * a + Csrc * b⌉ : ℝ) ≤ A * a + Csrc * b + 1 :=
    (Int.ceil_lt_add_one _).le
  linarith only [hlt]

/-- The entry constant `C` of `t.polynomial.entry`, assembled from the fixed constants
`A, B, Cg, Cresp, Csrc` and the logarithmic normalisation `(3 + d) / log₃ 2`. -/
@[expose]
noncomputable def entryConst (A B Cg Cresp Csrc : ℝ) (d : ℕ) : ℝ :=
  A + B + Cg + Cresp + 2 * Csrc + (3 + d) / Real.logb 3 2

/-- The entry constant is positive as soon as `Cg > 0` and the remaining constants are
nonnegative. -/
theorem entryConst_pos (A B Cg Cresp Csrc : ℝ) (d : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hCg : 0 < Cg) (hCresp : 0 ≤ Cresp) (hCsrc : 0 ≤ Csrc) :
    0 < entryConst A B Cg Cresp Csrc d := by
  have hL : 0 < Real.logb 3 2 := zero_lt_logb_three_two
  have hterm : 0 < (3 + (d : ℝ)) / Real.logb 3 2 := div_pos (by positivity) hL
  unfold entryConst
  linarith only [hA, hB, hCg, hCresp, hCsrc, hterm]

/-- The real terminal scale of `t.polynomial.entry`: if the integer terminal `t` is bounded by
`j + ⌈(B + Cg) * a⌉` and `m - t` by `⌈Cresp * a⌉`, then `m` is at most the corresponding real
logarithmic expression with two units of rounding slack. -/
theorem terminal_le_real (j t m : ℤ) (B Cg Cresp a : ℝ)
    (ht : t ≤ j + ⌈(B + Cg) * a⌉) (hm : m - t ≤ ⌈Cresp * a⌉) :
    (m : ℝ) ≤ j + (B + Cg) * a + Cresp * a + 2 := by
  have ht' : (t : ℝ) ≤ (j : ℝ) + ((⌈(B + Cg) * a⌉ : ℤ) : ℝ) := by
    have h : ((t : ℤ) : ℝ) ≤ ((j + ⌈(B + Cg) * a⌉ : ℤ) : ℝ) := Int.cast_le.mpr ht
    push_cast at h
    exact h
  have hm' : (m : ℝ) - (t : ℝ) ≤ ((⌈Cresp * a⌉ : ℤ) : ℝ) := by
    have h : ((m - t : ℤ) : ℝ) ≤ ((⌈Cresp * a⌉ : ℤ) : ℝ) := Int.cast_le.mpr hm
    push_cast at h
    exact h
  have h1 : ((⌈(B + Cg) * a⌉ : ℤ) : ℝ) ≤ (B + Cg) * a + 1 :=
    (Int.ceil_lt_add_one _).le
  have h2 : ((⌈Cresp * a⌉ : ℤ) : ℝ) ≤ Cresp * a + 1 :=
    (Int.ceil_lt_add_one _).le
  linarith only [ht', hm', h1, h2]

/-- The real entry bound of `t.polynomial.entry`: the terminal value `m`, already bounded by
the sum of the entry scale and the response and terminal scales, is dominated by the entry
constant times the logarithmic scale `c = log₃ (2 + Π K)`. -/
theorem entry_bound_real (A B Cg Cresp Csrc a b c : ℝ) (d : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbc : b ≤ 2 * c) (hc : Real.logb 3 2 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCg : 0 ≤ Cg) (hCresp : 0 ≤ Cresp) (hCsrc : 0 ≤ Csrc)
    (m : ℝ) (hm : m ≤ A * a + Csrc * b + 1 + d + (B + Cg) * a + Cresp * a + 2) :
    m ≤ entryConst A B Cg Cresp Csrc d * c := by
  have hAa : A * a ≤ A * c := mul_le_mul (le_refl A) hac ha hA
  have hCb : Csrc * b ≤ 2 * Csrc * c :=
    (mul_le_mul (le_refl Csrc) hbc hb hCsrc).trans (le_of_eq (by ring))
  have hBCa : (B + Cg) * a ≤ (B + Cg) * c :=
    mul_le_mul (le_refl (B + Cg)) hac ha (by linarith only [hB, hCg])
  have hCa : Cresp * a ≤ Cresp * c := mul_le_mul (le_refl Cresp) hac ha hCresp
  have hd : 3 + (d : ℝ) ≤ (3 + (d : ℝ)) / Real.logb 3 2 * c :=
    le_div_logb_mul (3 + (d : ℝ)) c (by positivity) hc
  unfold entryConst
  linarith only [hm, hAa, hCb, hBCa, hCa, hd]

/-- Integer form of the entry bound: an integer `m` bounded in `ℝ` by `C * c` is bounded by
the integer ceiling `⌈C * c⌉`. -/
theorem entry_bound_int (C c : ℝ) (m : ℤ) (h : (m : ℝ) ≤ C * c) : m ≤ ⌈C * c⌉ := by
  have h2 : (m : ℝ) ≤ ((⌈C * c⌉ : ℤ) : ℝ) := h.trans (Int.le_ceil (C * c))
  exact Int.cast_le.mp h2

/-- The terminal scale exceeds every earlier scale: if `j + ⌈B * a⌉ ≤ s < t < m`, then
`j ≤ m`. -/
theorem scale_le_terminal (j s t m : ℤ) (B a : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hs : j + ⌈B * a⌉ ≤ s) (hst : s < t) (htm : t < m) : j ≤ m := by
  have hceil : 0 ≤ ⌈B * a⌉ := Int.ceil_nonneg (mul_nonneg hB ha)
  omega

end HCPolySupport.HighContrast.Multiscale
