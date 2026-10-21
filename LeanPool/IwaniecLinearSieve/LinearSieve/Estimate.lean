/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.PrimeSums.Error
public import LeanPool.IwaniecLinearSieve.Rosser
import LeanPool.IwaniecLinearSieve.LinearSieve.Calculus
import LeanPool.IwaniecLinearSieve.LinearSieve.LemmaEleven
import LeanPool.IwaniecLinearSieve.LinearSieve.TheoremFive
import LeanPool.IwaniecLinearSieve.LinearSieve.TheoremFour
import Mathlib.Algebra.Order.Star.Real

/-!
# The linear sieve at level `C₀ z²` ([I71, Theorems 4–5]; [I78, Lemma 2])

With `y = C₀ z²` the sifting parameter is `s = log y / log z = 2 + log C₀ / log z`. Theorem 4,
`f(s) ≤ s - 3 log(s - 1)` (from `f(2) = 2`) and `R_asymp` show that the deficit `R(z) - V⁻(y, z)`
of the lower-bound sieve is at most `R(z) (1 - 1/log z)` once `log C₀` exceeds the error constant
of Theorem 4, so the main term is `≥ R(z)/log z`; Theorem 5 bounds the support by `≪ z²/log² z`.
-/

@[expose] public section

open Real Filter Finset

namespace IwaniecLinearSieve

/-- The estimates for Rosser's lower-bound sieve at level `y = C₀ z²` which [I78, Lemma 2] quotes
from [I71]: with `s = log y / log z = 2 + log C₀ / log z`,

* (6) `∑_{n ∣ P} σ_n / φ(n) = (∑_{d ∈ D⁻} μ(d)/d) / R(z) ≥ c / log z`, i.e.
  `R(z) - ∑_{d ∈ D⁻} μ(d)/d ≤ R(z) (1 - c / log z)`;
* (5) `∑ |λ_n| = |D⁻| ≪ y / log² y ≪ z² / log² z`,

for all `z ≥ z₀`. -/
def LinearSieveEstimate : Prop :=
  ∃ C₀ c K z₀ : ℝ, 0 < c ∧ ∀ z ≥ z₀,
    R z - rosserMain true (C₀ * z ^ 2) z ≤ R z * (1 - c / log z) ∧
      (#(rosserSet true (C₀ * z ^ 2) z) : ℝ) ≤ K * z ^ 2 / log z ^ 2

/-- `y^{1/s} = z` for `y = C₀ z²` and `s = log y / log z`. -/
theorem rpow_one_div_log_div {y z : ℝ} (hy : 0 < y) (hz : 1 < z) (hyl : log y ≠ 0) :
    y ^ (1 / (log y / log z)) = z := by
  have hlz : log z ≠ 0 := (log_pos hz).ne'
  rw [rpow_def_of_pos hy, show log y * (1 / (log y / log z)) = log z by field_simp,
    exp_log (by linarith)]

/-- `log (1 + x) ≥ x / (1 + x)` for `x ≥ 0`. -/
theorem div_one_add_le_log_one_add {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ log (1 + x) := by
  have h := log_le_sub_one_of_pos (show 0 < (1 + x)⁻¹ by positivity)
  rw [log_inv] at h
  have : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by field_simp; ring
  linarith

/-- If `0 ≤ x ≤ 1/2` and `s ≥ 2 + x`, then `log(s - 1) ≥ 2x/3`.
This supplies the logarithmic gain in the linear sieve estimate and Theorem 2. -/
theorem two_mul_div_three_le_log_sub_one {x s : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hs : 2 + x ≤ s) : 2 * x / 3 ≤ log (s - 1) := by
  calc 2 * x / 3 = x / (3 / 2) := by ring
    _ ≤ x / (1 + x) :=
        div_le_div_of_nonneg_left hx (by positivity) (by linarith only [hxhalf])
    _ ≤ log (1 + x) := div_one_add_le_log_one_add hx
    _ ≤ log (s - 1) := log_le_log (by positivity) (by linarith only [hs])

/-- `pntE z · log z → 0`. -/
theorem tendsto_pntE_mul_log : Tendsto (fun z => pntE z * log z) atTop (nhds 0) := by
  have hu : Tendsto (fun z : ℝ => pntκ * √(log z)) atTop atTop :=
    (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop pntκ_pos
  have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hu
  have h' := h.div_const (pntκ ^ 2)
  rw [zero_div] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with z hz
  have hl : 0 ≤ log z := log_nonneg hz
  simp only [Function.comp, pntE]
  rw [mul_pow, sq_sqrt hl, neg_mul]
  field_simp [pntκ_pos.ne']

/-- For `2 ≤ s ≤ 5/2`, choosing `A = B + 5` absorbs the bounded sieve error `B`
and leaves a saving of `4/ℓ²`. -/
theorem sieve_error_absorption {A B s ℓ : ℝ} (hA : A = B + 5) (hB : 0 ≤ B)
    (hs2 : 2 ≤ s) (hs25 : s ≤ 5 / 2) (hℓ : 0 < ℓ) :
    (s - 2 * A / ℓ) / (s * ℓ) + B / (s * ℓ) ^ 2 ≤ 1 / ℓ - 4 / ℓ ^ 2 := by
  have hs0 : 0 < s := by linarith only [hs2]
  have hkey : 4 * s ^ 2 ≤ 2 * A * s - B := by
    have hmargin : 2 * A * s - B - 4 * s ^ 2 =
        B * (2 * s - 1) + 2 * s * (5 - 2 * s) := by rw [hA]; ring
    have hBterm := mul_nonneg hB (by linarith only [hs2] : (0 : ℝ) ≤ 2 * s - 1)
    have hsterm := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * s)
      (by linarith only [hs25] : (0 : ℝ) ≤ 5 - 2 * s)
    linarith only [hmargin, hBterm, hsterm]
  have hsaving : 4 / ℓ ^ 2 ≤ (2 * A * s - B) / (s ^ 2 * ℓ ^ 2) := by
    calc 4 / ℓ ^ 2 = (4 * s ^ 2) / (s ^ 2 * ℓ ^ 2) := by field_simp
      _ ≤ (2 * A * s - B) / (s ^ 2 * ℓ ^ 2) :=
          div_le_div_of_nonneg_right hkey (by positivity)
  calc (s - 2 * A / ℓ) / (s * ℓ) + B / (s * ℓ) ^ 2 =
      1 / ℓ - (2 * A * s - B) / (s ^ 2 * ℓ ^ 2) := by field_simp; ring
    _ ≤ 1 / ℓ - 4 / ℓ ^ 2 := sub_le_sub le_rfl hsaving

/-- If the PNT error `e` satisfies `eℓ ≤ 3c`, the saving `4c/ℓ²` leaves the
factor `1 - 1/ℓ` against the lower estimate `(c - e)/ℓ` for `R(z)`. -/
theorem pnt_error_absorption {c e ℓ : ℝ} (hℓ : 0 < ℓ) (he0 : 0 ≤ e)
    (he : e * ℓ ≤ 3 * c) :
    c / ℓ - 4 * c / ℓ ^ 2 ≤ (c - e) / ℓ * (1 - 1 / ℓ) := by
  have herror : e / ℓ ≤ 3 * c / ℓ ^ 2 := by
    calc e / ℓ = (e * ℓ) / ℓ ^ 2 := by field_simp
      _ ≤ 3 * c / ℓ ^ 2 := div_le_div_of_nonneg_right he (sq_nonneg ℓ)
  have hremaining : 0 ≤ e / ℓ ^ 2 := div_nonneg he0 (sq_nonneg ℓ)
  have hsplit : 4 * c / ℓ ^ 2 = c / ℓ ^ 2 + 3 * c / ℓ ^ 2 := by ring
  calc c / ℓ - 4 * c / ℓ ^ 2
      ≤ c / ℓ - c / ℓ ^ 2 - e / ℓ + e / ℓ ^ 2 := by
        linarith only [herror, hremaining, hsplit]
    _ = (c - e) / ℓ * (1 - 1 / ℓ) := by field_simp; ring

/-- [I78, Lemma 2], from [I71, Theorems 4 and 5]: at level `C₀ z²` the
Rosser lower-bound sieve leaves a main term `≫ R(z)/log z`, and its support has size
`≪ z² / log² z`. -/
theorem linearSieveEstimate : LinearSieveEstimate := by
  obtain ⟨cR, hcR, CR, hR⟩ := R_asymp
  have hCR : 0 ≤ CR := by
    have h2 := hR 2 le_rfl
    exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans h2) (pntE_pos 2)
  obtain ⟨c₇, hc₇, h4⟩ := theorem4 hcR hR
  obtain ⟨K, y₀, h5⟩ := theorem5_card_rosserSet_le
  set D := (1 + 9 * Real.log 3 ^ 5) ^ (15 : ℝ) with hD
  have hD0 : 0 ≤ D := by positivity
  set B := 2 * c₇ * D with hB
  have hB0 : 0 ≤ B := by positivity
  set A := B + 5 with hA
  set C₀ := exp A with hC₀
  have hC₀0 : 0 < C₀ := exp_pos A
  clear_value D B A C₀
  have hyz : Tendsto (fun z : ℝ => C₀ * z ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop hC₀0
  have hev : ∀ᶠ z : ℝ in atTop, 2 * A ≤ log z ∧ 2 ≤ z ∧ CR * pntE z * log z ≤ 3 * cR ∧
      y₀ ≤ C₀ * z ^ 2 ∧ 3 ≤ xi (C₀ * z ^ 2) := by
    refine (tendsto_log_atTop.eventually_ge_atTop (2 * A)).and
      ((eventually_ge_atTop 2).and ?_)
    refine (((tendsto_pntE_mul_log.const_mul CR).eventually
      (eventually_le_nhds (show CR * 0 < 3 * cR by linarith))).mono
        fun z hz => by linarith).and ?_
    exact (hyz.eventually_ge_atTop y₀).and ((tendsto_xi.comp hyz).eventually_ge_atTop 3)
  obtain ⟨z₀, hz₀⟩ := eventually_atTop.1 hev
  refine ⟨C₀, 1, |K| * C₀, z₀, one_pos, fun z hz => ?_⟩
  obtain ⟨hlz, hz2, hpnt, hy₀, hxi⟩ := hz₀ z hz
  set ℓ := log z with hℓ
  set y := C₀ * z ^ 2 with hy
  have hA5 : 5 ≤ A := by linarith
  have hℓ10 : 10 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hz1 : 1 < z := by linarith
  have hy0 : 0 < y := by positivity
  have hL : log y = A + 2 * ℓ := by
    rw [hy, log_mul hC₀0.ne' (by positivity), log_pow, hC₀, log_exp]; push_cast; ring
  set s := log y / ℓ with hs
  have hsℓ : s * ℓ = log y := by rw [hs]; field_simp
  have hs2 : 2 ≤ s := by rw [hs, le_div_iff₀ hℓ0]; linarith
  have hs25 : s ≤ 5 / 2 := by rw [hs, div_le_iff₀ hℓ0]; linarith
  have hzs : y ^ (1 / s) = z := rpow_one_div_log_div hy0 hz1 (by rw [hL]; positivity)
  clear_value s y ℓ
  have hL1 : 1 ≤ log y := by rw [hL]; linarith
  constructor
  · -- main term
    set r := #(primesLT z) + 1
    have hfail := (fail_eq_of_card_lt (z := z) (r := r) (by omega) y).1
    have hy1 : 1 < y := by
      have hz21 : 1 < z ^ 2 := by nlinarith
      have hC₀1 : 1 ≤ C₀ := by rw [hC₀]; exact one_le_exp (by linarith)
      rw [hy]; nlinarith
    have h4' := h4 r true y s hy1 (by simpa [sMin] using hs2) (by linarith)
    rw [hzs, hfail] at h4'
    -- the main function
    have hf : fSieve s ≤ s - 3 * log (s - 1) := by
      have := one_sub_fSieve_div_ge s ⟨hs2, by linarith⟩
      have hs0 : 0 < s := by linarith
      rw [ge_iff_le, div_le_iff₀ hs0, sub_mul, div_mul_cancel₀ _ hs0.ne'] at this
      linarith
    have hlog : 2 * A / (3 * ℓ) ≤ log (s - 1) := by
      have hx : s - 1 = 1 + A / ℓ := by
        rw [hs, hL]; field_simp; ring
      have hxA : A / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ0]; linarith only [hlz]
      calc 2 * A / (3 * ℓ) = 2 * (A / ℓ) / 3 := by ring
        _ ≤ log (s - 1) :=
            two_mul_div_three_le_log_sub_one (by positivity) hxA (by linarith only [hx])
    -- the error term
    have herr : c₇ * ((r : ℝ) / (r + 1)) * delta s y * errMaj true s ≤ B := by
      have hδ : delta s y ≤ D := hD ▸ delta_le_of_le_three (s := s) (by linarith) (by linarith) hL1
      have hδ0 := delta_pos (by linarith : (1 : ℝ) ≤ s) y
      have hG := errMaj_le_two true s
      have hG0 := (errMaj_pos true s).le
      have hφ : (r : ℝ) / (r + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have hφ0 : (0 : ℝ) ≤ (r : ℝ) / (r + 1) := by positivity
      calc c₇ * ((r : ℝ) / (r + 1)) * delta s y * errMaj true s ≤ c₇ * 1 * D * 2 := by
            gcongr
        _ = B := by rw [hB]; ring
    have hdef : R z - rosserMain true y z ≤ cR / ℓ - 4 * cR / ℓ ^ 2 := by
      refine h4'.trans ?_
      have hmain : mainMaj true s / log y + c₇ * ((r : ℝ) / (r + 1)) * delta s y *
          errMaj true s / log y ^ 2 ≤ (s - 2 * A / ℓ) / log y + B / log y ^ 2 := by
        rw [mainMaj_true]
        have h3 : 3 * (2 * A / (3 * ℓ)) = 2 * A / ℓ := by field_simp
        gcongr
        linarith only [hf, hlog, h3]
      have hfin : (s - 2 * A / ℓ) / log y + B / log y ^ 2 ≤ 1 / ℓ - 4 / ℓ ^ 2 := by
        rw [← hsℓ]
        exact sieve_error_absorption hA hB0 hs2 hs25 hℓ0
      calc cR * (mainMaj true s / log y + c₇ * ((r : ℝ) / (r + 1)) * delta s y *
            errMaj true s / log y ^ 2) ≤ cR * (1 / ℓ - 4 / ℓ ^ 2) := by
            exact mul_le_mul_of_nonneg_left (hmain.trans hfin) hcR.le
        _ = cR / ℓ - 4 * cR / ℓ ^ 2 := by ring
    -- The PNT comparison converts the deficit estimate into a bound relative to `R(z)`.
    have hRz : (cR - CR * pntE z) / ℓ ≤ R z := by
      rw [div_le_iff₀ hℓ0]
      have hRlower := (abs_le.1 (hR z hz2)).1
      rw [← hℓ] at hRlower
      linarith only [hRlower]
    have h1 : 0 ≤ 1 - 1 / ℓ := by
      rw [sub_nonneg, div_le_one hℓ0]; linarith
    calc R z - rosserMain true y z ≤ cR / ℓ - 4 * cR / ℓ ^ 2 := hdef
      _ ≤ (cR - CR * pntE z) / ℓ * (1 - 1 / ℓ) :=
          pnt_error_absorption hℓ0 (mul_nonneg hCR (pntE_pos z).le) hpnt
      _ ≤ R z * (1 - 1 / ℓ) := mul_le_mul_of_nonneg_right hRz h1
  · -- support
    have h := h5 y hy₀ s ⟨hs2, by linarith⟩
    rw [hzs] at h
    refine h.trans ?_
    have hLℓ : ℓ ^ 2 ≤ log y ^ 2 := by
      rw [hL]; exact pow_le_pow_left₀ hℓ0.le (by linarith) 2
    calc K * y / log y ^ 2 ≤ |K| * y / log y ^ 2 := by
          gcongr; exact le_abs_self K
      _ ≤ |K| * y / ℓ ^ 2 := by
          gcongr
      _ = |K| * C₀ * z ^ 2 / ℓ ^ 2 := by rw [hy]; ring

end IwaniecLinearSieve
