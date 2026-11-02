/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Real.Sqrt

/-!
# LocalizationParams

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the corrected recurrence parameters at a free gap multiplier

Source displays in ABK26:

* `e.recurrence.params` (label; display) fixes the meso scale `n:= m - h - 16
  ceil|log_3 gamma|` and asserts `m - n <= 8 gamma^{-1}`, "increasing `M =
  M(d)` in `e.cgamma.constraints` if necessary";
* `e.lower.bound.principal.one.pre` (label; display) consumes two `gamma^6`
  remainders, both controlled by `3^{-(m-h-n)/4}`;

## The corrected multiplier, and the arithmetic re-verified here

The printed multiplier `16` is too small: at that choice `3^{-(m-h-n)/4} = 3^{-4
ceil|log_3 gamma|} in (gamma^4/81, gamma^4]` and `gamma^4 <= gamma^6` is false
on `(0,1)`.  The minimal correction replaces `16` by any `a >= 28`; the
development adopts `a = 32`.  This module renders `n` at a **free** multiplier
`a` and proves, at explicit gates, exactly the facts Steps 2 and 3 consume.

1. The quadratic is printed as "`2x - 2ax - a >= 0` in `sqrt x`".  With
   `u := sqrt x`, `x := gamma^{-1}`, the inequality the argument needs is
   `a(2u+1) <= 2u^2`, i.e. **`2u^2 - 2au - a >= 0`**; the printed middle term
   should be `2au`, not `2ax`.
2. The sufficient condition is often read as an equivalence ("i.e.  `sqrt x >=
   a+1`").  It is **sufficient, not necessary**: the positive root of `2u^2 -
   2au - a` is `(a + sqrt(a^2+2a))/2 < a + 1/2`.  Only sufficiency is claimed
   below, and it is what the coverage constant `(a+1)^2` records: `289` at the
   printed `a = 16`, `1089` at the adopted `a = 32`.

Both auxiliary estimates are re-derived here from
`Real.log_le_sub_one_of_pos` alone: `ceil(log_3 x) <= 2 sqrt x + 1` (via `log x
<= 2(sqrt x - 1)`, `log 3 >= 1`) and `ceil(log_3 gamma^{-1}) * gamma^{1/4} <=
4` (via `log x <= 4(x^{1/4} - 1)`).

## What is proved

* `logThreeCeil`, `recurrenceGap`, `recurrenceMesoScale` -- the corrected buffer
  `n := m - h - a * ceil|log_3 gamma|` as a function of a free `a : Nat`.
* `rpow_three_neg_recurrenceGap_div_four_le_rpow` and its `a >= 28` instance --
  the Step-3 gate `3^{-(m-h-n)/4} <= gamma^{a/4} <= gamma^7`.
* `recurrenceGap_le_two_mul_inv`, `recurrenceMesoScale_budget` -- the coverage
  condition `gamma^{-1} >= (a+1)^2`'s budget, in `c_star`-free form: the
  constant `c_star` is carried into the conclusion `(6 c_star + 2) gamma^{-1}`
  rather than capped; see the recorded delta below.
* `natCast_le_recurrenceGap_of_rpow_le`, `dim_add_three_le_recurrenceGap` -- the
  `d + 3 <= m - h - n` check, at the explicit gate `3^{d+3} <= gamma^{-1}`.

## Divergences from the printed statement

* **The corrected multiplier is encoded explicitly.**  Nothing below is
  stated at the printed multiplier `16`.  Every statement carries `a` as a free
  natural number and every use of `a >= 28` is an explicit hypothesis.
* **The `c_star <= 1` step is refused; the constant moves instead.**  The
  printed argument passes from `h <= 6 c_star gamma^{-1}` to
  `h <= 6 gamma^{-1}` silently, i.e. it uses `c_star <= 1`.  That bound is
  underivable here by the second-moment route, and the only proved cap is
  `Provider.Disorder.cstar_le_three_halves`, `c_star <= 3/2`.  No declaration in
  this module carries a `c_star <= 1` hypothesis.  Instead
  `recurrenceMesoScale_budget` keeps `c_star` in the conclusion, at
  `(6 c_star + 2) gamma^{-1}` and with no cap assumed, so a caller holding the
  proved cap reads off `11 gamma^{-1}` where the printed argument reads
  `8 gamma^{-1}`.
* **`d + 3`, not `d + 2`.**  The stage numeric is often quoted as
  `d + 2 <= (a ceil|log_3 gamma|).toNat`.  The statement below is proved for an
  arbitrary `N` and instantiated at `d + 3`, which is what the localization
  argument needs; the `d + 2` form is the same lemma at a smaller `N`.

## What is not proved here

* **The `gamma`-threshold bridge is open.**  Nothing here derives `hcover` or
  `hgate` from `e.cgamma.constraints`.  Both thresholds are stated as binders
  precisely so that the missing bridge stays visible at every instantiation
  site; closing it is not attempted in this module.
* **`c_star <= 1` is NOT available**, so the printed budget constant `8` is not
  reachable by this route; the proved cap `c_star <= 3/2` gives `11`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

/-! ## The triadic logarithmic ceiling and the corrected buffer -/

/-- `ceil |log_3 gamma|`, as a natural number.  On `0 < gamma <= 1` this is
`ceil (log_3 gamma^{-1})`, which is the manuscript's quantity. -/
def logThreeCeil (gamma : ℝ) : ℕ := ⌈Real.logb 3 gamma⁻¹⌉₊

/-- The scale gap `m - h - n = a * ceil|log_3 gamma|` of the corrected
`e.recurrence.params`, at a **free** multiplier `a`.  The printed choice is `a
= 16`, any `a >= 28` is admissible, and the development adopts `a = 32`. -/
def recurrenceGap (a : ℕ) (gamma : ℝ) : ℕ := a * logThreeCeil gamma

/-- The corrected buffer `n := m - h - a * ceil|log_3 gamma|`. -/
def recurrenceMesoScale (a : ℕ) (gamma : ℝ) (m h : ℤ) : ℤ :=
  m - h - (recurrenceGap a gamma : ℤ)

/-- The floor of the admissible multiplier gate. -/
def recurrenceGapMultiplierFloor : ℕ := 28

/-- The round multiplier adopted by the development. -/
def recurrenceGapMultiplier : ℕ := 32

theorem recurrenceGapMultiplierFloor_le_recurrenceGapMultiplier :
    recurrenceGapMultiplierFloor ≤ recurrenceGapMultiplier := by
  norm_num [recurrenceGapMultiplierFloor, recurrenceGapMultiplier]

@[simp] theorem sub_recurrenceMesoScale (a : ℕ) (gamma : ℝ) (m h : ℤ) :
    m - h - recurrenceMesoScale a gamma m h = (recurrenceGap a gamma : ℤ) := by
  simp [recurrenceMesoScale]

theorem recurrenceMesoScale_le (a : ℕ) (gamma : ℝ) (m h : ℤ) :
    recurrenceMesoScale a gamma m h ≤ m - h := by
  simp only [recurrenceMesoScale]
  omega

/-! ## Elementary facts about the ceiling -/

private theorem one_le_inv_gamma {gamma : ℝ} (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    (1 : ℝ) ≤ gamma⁻¹ := by
  rw [le_inv_comm₀ (by norm_num) hgamma0]
  simpa using hgamma1

private theorem logb_three_inv_nonneg {gamma : ℝ} (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    0 ≤ Real.logb 3 gamma⁻¹ :=
  Real.logb_nonneg (by norm_num) (one_le_inv_gamma hgamma0 hgamma1)

theorem logb_le_logThreeCeil (gamma : ℝ) :
    Real.logb 3 gamma⁻¹ ≤ (logThreeCeil gamma : ℝ) :=
  Nat.le_ceil _

theorem logThreeCeil_lt_logb_add_one {gamma : ℝ} (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    (logThreeCeil gamma : ℝ) < Real.logb 3 gamma⁻¹ + 1 :=
  Nat.ceil_lt_add_one (logb_three_inv_nonneg hgamma0 hgamma1)

/-! ## The two analytic cores -/

private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h := (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr hexp
  linarith

private theorem logb_three_le_log {x : ℝ} (hx : 1 ≤ x) : Real.logb 3 x ≤ Real.log x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [← Real.log_div_log]
  exact div_le_self hlog one_le_log_three

private theorem log_le_two_mul_sqrt_sub_one {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 2 * (Real.sqrt x - 1) := by
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hsqrt
  rw [Real.log_sqrt hx.le] at h
  linarith

/-! ## The coverage condition -/

theorem logThreeCeil_le_two_mul_sqrt_add_one {gamma : ℝ} (hgamma0 : 0 < gamma)
    (hgamma1 : gamma ≤ 1) :
    (logThreeCeil gamma : ℝ) ≤ 2 * Real.sqrt gamma⁻¹ + 1 := by
  have hx : (1 : ℝ) ≤ gamma⁻¹ := one_le_inv_gamma hgamma0 hgamma1
  have hx0 : (0 : ℝ) < gamma⁻¹ := lt_of_lt_of_le one_pos hx
  have hceil := logThreeCeil_lt_logb_add_one hgamma0 hgamma1
  have hlogb := logb_three_le_log hx
  have hlog := log_le_two_mul_sqrt_sub_one hx0
  linarith

/-- The pure-algebra core of the coverage condition: at `u >= a + 1` the
quadratic `2u^2 - 2au - a` is nonnegative. -/
private theorem coverage_core {a u : ℝ} (ha : 0 ≤ a) (hu : a + 1 ≤ u) :
    a * (2 * u + 1) ≤ 2 * u ^ 2 := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u) (by linarith : (0 : ℝ) ≤ u - a - 1)]

theorem recurrenceGap_le_two_mul_inv (a : ℕ) {gamma : ℝ} (hgamma0 : 0 < gamma)
    (hgamma1 : gamma ≤ 1) (hcover : ((a : ℝ) + 1) ^ 2 ≤ gamma⁻¹) :
    (recurrenceGap a gamma : ℝ) ≤ 2 * gamma⁻¹ := by
  have hx : (1 : ℝ) ≤ gamma⁻¹ := one_le_inv_gamma hgamma0 hgamma1
  have hx0 : (0 : ℝ) ≤ gamma⁻¹ := le_trans zero_le_one hx
  have hu : (a : ℝ) + 1 ≤ Real.sqrt gamma⁻¹ :=
    (Real.le_sqrt (by positivity) hx0).mpr hcover
  have hsq : Real.sqrt gamma⁻¹ ^ 2 = gamma⁻¹ := Real.sq_sqrt hx0
  have hceil := logThreeCeil_le_two_mul_sqrt_add_one hgamma0 hgamma1
  have hcore := coverage_core (a := (a : ℝ)) (u := Real.sqrt gamma⁻¹) (by positivity) hu
  have hprod : (a : ℝ) * (logThreeCeil gamma : ℝ) ≤ (a : ℝ) * (2 * Real.sqrt gamma⁻¹ + 1) :=
    mul_le_mul_of_nonneg_left hceil (by positivity)
  have hcast : (recurrenceGap a gamma : ℝ) = (a : ℝ) * (logThreeCeil gamma : ℝ) := by
    simp [recurrenceGap]
  rw [hcast, ← hsq]
  linarith

/-- **The budget at the corrected gap, in `c_star`-free form.**

: `hgamma0`, `hgamma1`, `hcover` and the shell-width cap `hshell` are
caller-supplied and are not discharged here.  **No cap on `c_star` is
assumed**: the constant `c_star` is carried into the conclusion, so the
statement is available at whatever cap the caller actually holds. -/
theorem recurrenceMesoScale_budget (a : ℕ) {gamma cstar : ℝ} (m h : ℤ)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hcover : ((a : ℝ) + 1) ^ 2 ≤ gamma⁻¹)
    (hshell : (h : ℝ) ≤ 6 * cstar * gamma⁻¹) :
    ((m - recurrenceMesoScale a gamma m h : ℤ) : ℝ) ≤ (6 * cstar + 2) * gamma⁻¹ := by
  have hgap := recurrenceGap_le_two_mul_inv a hgamma0 hgamma1 hcover
  have hcast : ((m - recurrenceMesoScale a gamma m h : ℤ) : ℝ) =
      (h : ℝ) + (recurrenceGap a gamma : ℝ) := by
    simp only [recurrenceMesoScale]
    push_cast
    ring
  have hexp : (6 * cstar + 2) * gamma⁻¹ = 6 * cstar * gamma⁻¹ + 2 * gamma⁻¹ := by ring
  rw [hcast, hexp]
  linarith

/-! ## The Step-3 gap gate -/

/-- The master gate: for any exponent `t` with `0 <= t <= a/4`, the corrected gap
dominates `t` powers of `gamma^{-1}` in the base-`3` scale. -/
private theorem inv_rpow_le_rpow_three_recurrenceGap_div_four {a : ℕ} {gamma t : ℝ}
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) (hta : t ≤ (a : ℝ) / 4) :
    gamma⁻¹ ^ t ≤ (3 : ℝ) ^ ((recurrenceGap a gamma : ℝ) / 4) := by
  have hx0 : (0 : ℝ) < gamma⁻¹ := inv_pos.mpr hgamma0
  have hL0 : 0 ≤ Real.logb 3 gamma⁻¹ := logb_three_inv_nonneg hgamma0 hgamma1
  have hceil := logb_le_logThreeCeil gamma
  have hcast : (recurrenceGap a gamma : ℝ) = (a : ℝ) * (logThreeCeil gamma : ℝ) := by
    simp [recurrenceGap]
  have hexp : Real.logb 3 gamma⁻¹ * t ≤ (recurrenceGap a gamma : ℝ) / 4 := by
    rw [hcast]
    have h1 : Real.logb 3 gamma⁻¹ * t ≤ Real.logb 3 gamma⁻¹ * ((a : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left hta hL0
    have h2 : Real.logb 3 gamma⁻¹ * ((a : ℝ) / 4) ≤
        (logThreeCeil gamma : ℝ) * ((a : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hceil (by positivity)
    linarith
  have hrepr : gamma⁻¹ = (3 : ℝ) ^ Real.logb 3 gamma⁻¹ :=
    (Real.rpow_logb (by norm_num) (by norm_num) hx0).symm
  calc gamma⁻¹ ^ t = ((3 : ℝ) ^ Real.logb 3 gamma⁻¹) ^ t := by rw [← hrepr]
    _ = (3 : ℝ) ^ (Real.logb 3 gamma⁻¹ * t) := (Real.rpow_mul (by norm_num) _ _).symm
    _ ≤ (3 : ℝ) ^ ((recurrenceGap a gamma : ℝ) / 4) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- **The Step-3 gap gate**: at the corrected gap `m - h - n = a ceil|log_3 gamma|`
one has `3^{-(m-h-n)/4} <= gamma^{a/4}`. -/
theorem rpow_three_neg_recurrenceGap_div_four_le_rpow (a : ℕ) {gamma t : ℝ}
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) (hta : t ≤ (a : ℝ) / 4) :
    (3 : ℝ) ^ (-((recurrenceGap a gamma : ℝ) / 4)) ≤ gamma ^ t := by
  have hmaster := inv_rpow_le_rpow_three_recurrenceGap_div_four
    (a := a) (gamma := gamma) (t := t) hgamma0 hgamma1 hta
  have hpos : (0 : ℝ) < gamma ^ t := Real.rpow_pos_of_pos hgamma0 t
  have hinv : gamma⁻¹ ^ t = (gamma ^ t)⁻¹ := Real.inv_rpow hgamma0.le t
  rw [Real.rpow_neg (by norm_num), inv_le_comm₀ (by positivity) hpos]
  rw [hinv] at hmaster
  exact hmaster

/-- The instance the two `gamma^6` remainders consume: at any multiplier `a >= 28`
the switch factor and the Young remainder are controlled by `gamma^7`, leaving
one spare power of `gamma` for the dimensional constant. -/
theorem rpow_three_neg_recurrenceGap_div_four_le_rpow_seven (a : ℕ) {gamma : ℝ}
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (ha : recurrenceGapMultiplierFloor ≤ a) :
    (3 : ℝ) ^ (-((recurrenceGap a gamma : ℝ) / 4)) ≤ gamma ^ (7 : ℝ) := by
  refine rpow_three_neg_recurrenceGap_div_four_le_rpow a hgamma0 hgamma1 ?_
  have h : (28 : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast (by simpa [recurrenceGapMultiplierFloor] using ha : (28 : ℕ) ≤ a)
  linarith

/-! ## The `d + 3` check -/

/-- If `gamma^{-1}` clears `3^N` then the corrected gap clears `N`. -/
theorem natCast_le_recurrenceGap_of_rpow_le {a N : ℕ} {gamma : ℝ} (hgamma0 : 0 < gamma)
    (ha : 1 ≤ a) (hgate : (3 : ℝ) ^ (N : ℝ) ≤ gamma⁻¹) :
    N ≤ recurrenceGap a gamma := by
  have hx0 : (0 : ℝ) < gamma⁻¹ := inv_pos.mpr hgamma0
  have hN : (N : ℝ) ≤ Real.logb 3 gamma⁻¹ :=
    (Real.le_logb_iff_rpow_le (by norm_num) hx0).mpr hgate
  have hceil : (N : ℝ) ≤ (logThreeCeil gamma : ℝ) :=
    le_trans hN (logb_le_logThreeCeil gamma)
  have hNle : N ≤ logThreeCeil gamma := by exact_mod_cast hceil
  calc N ≤ logThreeCeil gamma := hNle
    _ ≤ a * logThreeCeil gamma := Nat.le_mul_of_pos_left _ ha
    _ = recurrenceGap a gamma := rfl

/-- **The `d + 3 <= m - h - n` check**, at the explicit gate `3^{d+3} <= gamma^{-1}`.
Nothing below asserts that `e.cgamma.constraints` supplies the gate. -/
theorem dim_add_three_le_recurrenceGap {a : ℕ} (d : ℕ) {gamma : ℝ} (hgamma0 : 0 < gamma)
    (ha : 1 ≤ a) (hgate : (3 : ℝ) ^ ((d : ℝ) + 3) ≤ gamma⁻¹) :
    d + 3 ≤ recurrenceGap a gamma := by
  refine natCast_le_recurrenceGap_of_rpow_le (N := d + 3) hgamma0 ha ?_
  have hcast : ((d + 3 : ℕ) : ℝ) = (d : ℝ) + 3 := by push_cast; ring
  rw [hcast]
  exact hgate

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
