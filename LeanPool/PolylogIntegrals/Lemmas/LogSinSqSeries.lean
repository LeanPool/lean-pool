/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.ArctanTrilog
public import LeanPool.PolylogIntegrals.Lemmas.Fourier

/-!
# The integral `∫₀¹ (log³((1+r)/2) - log³((1-r)/2))/r dr`

This file evaluates the real integral that the radial argument of A015 produces:
`∫₀¹ (log³((1+r)/2) - log³((1-r)/2))/r dr = 2π⁴/15 + π² log² 2 - log⁴ 2/4 - 6 Li₄(1/2)`.

## Main results

* `LeanPolyLog.LogSinSq.integral_pow_mul_log_cube`: `∫₀¹ tᵐ log³ t dt = -6/(m+1)⁴`.
* `LeanPolyLog.LogSinSq.Lir_four_one`: `Li₄(1) = ζ(4) = π⁴/90`.
* `LeanPolyLog.LogSinSq.integral_log_cube_one_sub_div`:
  `∫₀¹ (log³((1-r)/2) + log³ 2)/r dr = -π⁴/15 - 6 log 2 ζ(3) - (π²/2) log² 2`.
* `LeanPolyLog.LogSinSq.integral_log_cube_one_add_div`:
  `∫₀¹ (log³((1+r)/2) + log³ 2)/r dr = π⁴/15 - 6 log 2 ζ(3) + (π²/2) log² 2 - log⁴ 2/4
  - 6 Li₄(1/2)`.
* `LeanPolyLog.LogSinSq.integral_log_cube_div`: the difference of the two.

## Proof sketch

Write `c = log 2`. Adding `c³` to both cubes makes each integrand bounded near `r = 0`.

* The `(1-r)` part: with `s = 1 - r` it becomes `∫₀¹ φ(s)/(1-s) ds`, where
  `φ(s) = log³(s/2) + c³ = log³ s - 3c log² s + 3c² log s ≤ 0`. Expanding `1/(1-s) = ∑ sⁿ` and
  integrating term by term with the moments `∫₀¹ sⁿ logᵏ s ds = (-1)ᵏ k!/(n+1)^(k+1)` gives
  `-6ζ(4) - 6c ζ(3) - 3c² ζ(2)`. This value is nonzero, so the integrand is integrable.
* The `(1+r)` part has the explicit antiderivative (with `ℓ = c - log(1+r)`, `w = 1/(1+r)`)
  `ℓ⁴/4 - c³ℓ + log(1-w)(c³ - ℓ³) - 3ℓ² Li₂(w) + 6ℓ Li₃(w) - 6 Li₄(w)`,
  where `log(1-w) (c³ - ℓ³) = (log r · log(1+r) - log²(1+r)) (ℓ² + ℓc + c²)` is continuous at
  `r = 0`. It runs from `-(3/4)c⁴ - 3c² ζ(2) + 6c ζ(3) - 6ζ(4)` at `r = 0` to `-c⁴ - 6 Li₄(1/2)`
  at `r = 1`. The integrand is nonnegative, so it is integrable.
* In the difference `ζ(3)` cancels.
-/

open Real MeasureTheory Set

namespace LeanPolyLog.LogSinSq

/-! ### The moments `∫₀¹ tᵐ log³ t dt` -/

/-- `t log³ t` is continuous on `[0, ∞)`: with `u = √(√t)` it equals `64 u (u log u)³`. -/
public theorem continuousOn_mul_log_cube : ContinuousOn (fun t : ℝ ↦ t * log t ^ 3) (Ici 0) := by
  have h : Continuous fun t : ℝ ↦ 64 * (√(√t) * (√(√t) * log √(√t)) ^ 3) :=
    continuous_const.mul ((continuous_sqrt.comp continuous_sqrt).mul
      ((continuous_mul_log.comp (continuous_sqrt.comp continuous_sqrt)).pow 3))
  refine h.continuousOn.congr fun t ht ↦ ?_
  have ht' : (0 : ℝ) ≤ t := ht
  have hs : 0 ≤ √t := sqrt_nonneg t
  have h4 : √(√t) ^ 4 = t := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_sqrt hs, sq_sqrt ht']
  dsimp only
  rw [log_sqrt hs, log_sqrt ht']
  linear_combination (-(log t ^ 3)) * h4

/-- An antiderivative of `tᵐ log³ t`. It is continuous on `[0, 1]` and vanishes at `0`. -/
@[expose] public noncomputable def powMulLogCubePrimitive (m : ℕ) (t : ℝ) : ℝ :=
  t ^ (m + 1) * log t ^ 3 / ((m : ℝ) + 1) - 3 * (t ^ (m + 1) * log t ^ 2) / ((m : ℝ) + 1) ^ 2 +
    6 * (t ^ (m + 1) * log t) / ((m : ℝ) + 1) ^ 3 - 6 * t ^ (m + 1) / ((m : ℝ) + 1) ^ 4

/-- Away from `0`, the derivative of `powMulLogCubePrimitive m` is `tᵐ log³ t`. -/
public theorem hasDerivAt_powMulLogCubePrimitive (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (powMulLogCubePrimitive m) (t ^ m * log t ^ 3) t := by
  have hl := hasDerivAt_log ht
  have hp := hasDerivAt_pow (m + 1) t
  have h1 := (hp.mul (hl.pow 3)).div_const ((m : ℝ) + 1)
  have h2 := ((hp.mul (hl.pow 2)).const_mul 3).div_const (((m : ℝ) + 1) ^ 2)
  have h3 := ((hp.mul hl).const_mul 6).div_const (((m : ℝ) + 1) ^ 3)
  have h4 := (hp.const_mul 6).div_const (((m : ℝ) + 1) ^ 4)
  refine (((h1.sub h2).add h3).sub h4).congr_deriv ?_
  simp only [Nat.add_sub_cancel, Pi.pow_apply]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  rw [pow_succ]
  field_simp
  ring

/-- `powMulLogCubePrimitive m` is continuous on `[0, 1]`. -/
public theorem continuousOn_powMulLogCubePrimitive (m : ℕ) :
    ContinuousOn (powMulLogCubePrimitive m) (Icc 0 1) := by
  have h3 : ContinuousOn (fun t : ℝ ↦ t ^ (m + 1) * log t ^ 3) (Icc 0 1) :=
    (((continuous_pow m).continuousOn.mul
      (continuousOn_mul_log_cube.mono Icc_subset_Ici_self))).congr
      fun t _ ↦ by simp only [Pi.mul_apply]; ring
  have h2 : ContinuousOn (fun t : ℝ ↦ t ^ (m + 1) * log t ^ 2) (Icc 0 1) :=
    (((continuous_pow m).continuousOn.mul
      (Arctan.continuousOn_mul_log_sq.mono Icc_subset_Ici_self))).congr
      fun t _ ↦ by simp only [Pi.mul_apply]; ring
  unfold powMulLogCubePrimitive
  refine (((h3.div_const _).sub ((h2.const_smul (3 : ℝ)).div_const _)).add ?_).sub ?_
  · exact (continuousOn_const.mul (LogTrig.continuous_pow_succ_mul_log m).continuousOn).div_const _
  · exact (continuousOn_const.mul (continuous_pow (m + 1)).continuousOn).div_const _

/-- `tᵐ log³ t` is integrable on `[0, 1]`: its negative is the nonnegative derivative of a
continuous function. -/
public theorem intervalIntegrable_pow_mul_log_cube (m : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ m * log t ^ 3) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have h := intervalIntegral.integrableOn_deriv_of_nonneg
    (continuousOn_powMulLogCubePrimitive m).neg
    (fun t ht ↦ (hasDerivAt_powMulLogCubePrimitive m ht.1.ne').neg)
    (fun t ht ↦ neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht.1.le m)
      (Odd.pow_nonpos (by decide) (log_nonpos ht.1.le ht.2.le))))
  simpa using h.neg

/-- `∫₀¹ tᵐ log³ t dt = -6/(m+1)⁴`. -/
public theorem integral_pow_mul_log_cube (m : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ m * log t ^ 3 = -(6 / ((m : ℝ) + 1) ^ 4) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_powMulLogCubePrimitive m)
    (fun t ht ↦ hasDerivAt_powMulLogCubePrimitive m ht.1.ne')
    (intervalIntegrable_pow_mul_log_cube m)]
  simp [powMulLogCubePrimitive]

/-! ### Zeta values -/

/-- `∑_{n ≥ 0} 1/(n+1)² = π²/6`. -/
public theorem hasSum_zeta_two_succ : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  simpa using h

/-- `∑_{n ≥ 0} 1/(n+1)⁴ = π⁴/90`. -/
public theorem hasSum_zeta_four_succ : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 4) (π ^ 4 / 90) := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_four
  simpa using h

/-- `Li₄(1) = ζ(4) = π⁴/90`. -/
public theorem Lir_four_one : Lir 4 1 = π ^ 4 / 90 := by
  unfold Lir
  simpa only [one_pow] using hasSum_zeta_four_succ.tsum_eq

/-- `ζ(3) ≥ 0`. -/
public theorem zeta3_nonneg : 0 ≤ zeta3 :=
  tsum_nonneg fun n ↦ by positivity

/-! ### The `(1 - r)` part -/

/-- `φ(s) = log³ s - 3 log 2 · log² s + 3 log² 2 · log s`, which is `log³(s/2) + log³ 2` for
`s > 0`. -/
@[expose] public noncomputable def phi (s : ℝ) : ℝ :=
  log s ^ 3 - 3 * log 2 * log s ^ 2 + 3 * log 2 ^ 2 * log s

/-- `sⁿ φ(s)` is integrable on `[0, 1]`. -/
public theorem intervalIntegrable_pow_mul_phi (n : ℕ) :
    IntervalIntegrable (fun s ↦ s ^ n * phi s) volume 0 1 := by
  have h := ((intervalIntegrable_pow_mul_log_cube n).sub
    ((Arctan.intervalIntegrable_pow_mul_log_sq n).const_mul (3 * log 2))).add
    ((Arctan.intervalIntegrable_pow_mul_log n).const_mul (3 * log 2 ^ 2))
  convert h using 1
  ext s
  simp only [phi]
  ring

/-- `∫₀¹ sⁿ φ(s) ds = -6/(n+1)⁴ - 6 log 2/(n+1)³ - 3 log² 2/(n+1)²`. -/
public theorem integral_pow_mul_phi (n : ℕ) :
    ∫ s in (0 : ℝ)..1, s ^ n * phi s =
      -(6 * (1 / ((n : ℝ) + 1) ^ 4)) - 6 * log 2 * (1 / ((n : ℝ) + 1) ^ 3)
        - 3 * log 2 ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
  have i1 := intervalIntegrable_pow_mul_log_cube n
  have i2 := (Arctan.intervalIntegrable_pow_mul_log_sq n).const_mul (3 * log 2)
  have i3 := (Arctan.intervalIntegrable_pow_mul_log n).const_mul (3 * log 2 ^ 2)
  have e : (fun s ↦ s ^ n * phi s) = fun s ↦ s ^ n * log s ^ 3 - 3 * log 2 * (s ^ n * log s ^ 2)
      + 3 * log 2 ^ 2 * (s ^ n * log s) := by
    ext s
    simp only [phi]
    ring
  rw [e, intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow_mul_log_cube, Arctan.integral_pow_mul_log_sq, Arctan.integral_pow_mul_log]
  ring

/-- `φ ≤ 0` on `[0, 1]`. -/
public theorem phi_nonpos {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : phi s ≤ 0 := by
  have hl : log s ≤ 0 := log_nonpos hs.1 hs.2
  have hc : 0 < log 2 := log_pos one_lt_two
  have h3 : log s ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) hl
  unfold phi
  nlinarith [sq_nonneg (log s), mul_nonneg hc.le (sq_nonneg (log s)),
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (log 2)) hl]

/-- `∫₀¹ ‖sⁿ φ(s)‖ ds = 6/(n+1)⁴ + 6 log 2/(n+1)³ + 3 log² 2/(n+1)²`. -/
public theorem integral_norm_pow_mul_phi (n : ℕ) :
    ∫ s in (0 : ℝ)..1, ‖s ^ n * phi s‖ =
      6 * (1 / ((n : ℝ) + 1) ^ 4) + 6 * log 2 * (1 / ((n : ℝ) + 1) ^ 3)
        + 3 * log 2 ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
  have h : ∫ s in (0 : ℝ)..1, ‖s ^ n * phi s‖ = ∫ s in (0 : ℝ)..1, -(s ^ n * phi s) := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le zero_le_one] at hs
    exact Real.norm_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hs.1 n) (phi_nonpos hs))
  rw [h, intervalIntegral.integral_neg, integral_pow_mul_phi]
  ring

/-- `∫₀¹ φ(s)/(1-s) ds = -π⁴/15 - 6 log 2 ζ(3) - (π²/2) log² 2`. -/
public theorem integral_phi_div_one_sub :
    ∫ s in (0 : ℝ)..1, phi s / (1 - s) =
      -(π ^ 4 / 15) - 6 * log 2 * zeta3 - π ^ 2 / 2 * log 2 ^ 2 := by
  have hs4 := (Dilog.summable_one_div_succ_pow (by norm_num : 2 ≤ 4))
  have hs3 := (Dilog.summable_one_div_succ_pow (by norm_num : 2 ≤ 3))
  have hs2 := (Dilog.summable_one_div_succ_pow (le_refl 2))
  have h := Arctan.hasSum_integral_div_one_sub (φ := phi) (q := fun s ↦ s)
    (fun y hy ↦ by rw [abs_of_pos hy.1]; exact hy.2) intervalIntegrable_pow_mul_phi
    (by
      simp only [integral_norm_pow_mul_phi]
      exact ((hs4.mul_left 6).add (hs3.mul_left (6 * log 2))).add (hs2.mul_left (3 * log 2 ^ 2)))
  simp only [integral_pow_mul_phi] at h
  refine h.unique ?_
  convert (((hasSum_zeta_four_succ.mul_left 6).neg.sub
    (Fourier.hasSum_zeta3.mul_left (6 * log 2))).sub
    (hasSum_zeta_two_succ.mul_left (3 * log 2 ^ 2))) using 1
  ring

/-- `∫₀¹ (log³((1-r)/2) + log³ 2)/r dr = -π⁴/15 - 6 log 2 ζ(3) - (π²/2) log² 2`. -/
public theorem integral_log_cube_one_sub_div :
    ∫ r in (0 : ℝ)..1, (log ((1 - r) / 2) ^ 3 + log 2 ^ 3) / r =
      -(π ^ 4 / 15) - 6 * log 2 * zeta3 - π ^ 2 / 2 * log 2 ^ 2 := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun s ↦ (log (s / 2) ^ 3 + log 2 ^ 3) / (1 - s)) 1 (a := 0) (b := 1)
  simp only [sub_sub_cancel, sub_zero, sub_self] at h
  rw [h, ← integral_phi_div_one_sub]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs ↦ ?_)
  rw [uIoc_of_le zero_le_one] at hs
  rw [log_div hs.1.ne' two_ne_zero, phi]
  ring

/-- `(log³((1-r)/2) + log³ 2)/r` is integrable on `[0, 1]`, since its integral is nonzero. -/
public theorem intervalIntegrable_log_cube_one_sub_div :
    IntervalIntegrable (fun r ↦ (log ((1 - r) / 2) ^ 3 + log 2 ^ 3) / r) volume 0 1 := by
  refine intervalIntegral.intervalIntegrable_of_integral_ne_zero ?_
  rw [integral_log_cube_one_sub_div]
  have hc : 0 < log 2 := log_pos one_lt_two
  have hz := zeta3_nonneg
  have hπ : 0 < π ^ 4 / 15 := by positivity
  nlinarith [mul_nonneg hc.le hz, mul_nonneg (sq_nonneg π) (sq_nonneg (log 2))]

/-! ### The `(1 + r)` part -/

/-- An antiderivative of `(log³((1+r)/2) + log³ 2)/r` for `r > 0`. With `c = log 2`,
`ℓ = c - log(1+r)` and `w = 1/(1+r)` it is
`ℓ⁴/4 - c³ℓ + (log r log(1+r) - log²(1+r)) (ℓ² + ℓc + c²) - 3ℓ² Li₂(w) + 6ℓ Li₃(w) - 6 Li₄(w)`. -/
@[expose] public noncomputable def plusPrimitive (r : ℝ) : ℝ :=
  (log 2 - log (1 + r)) ^ 4 / 4 - log 2 ^ 3 * (log 2 - log (1 + r))
    + (log r * log (1 + r) - log (1 + r) ^ 2) *
      ((log 2 - log (1 + r)) ^ 2 + (log 2 - log (1 + r)) * log 2 + log 2 ^ 2)
    - 3 * (log 2 - log (1 + r)) ^ 2 * Lir 2 (1 / (1 + r))
    + 6 * (log 2 - log (1 + r)) * Lir 3 (1 / (1 + r)) - 6 * Lir 4 (1 / (1 + r))

/-- For `r > 0`, `plusPrimitive' r = (log³((1+r)/2) + log³ 2)/r`. -/
public theorem hasDerivAt_plusPrimitive {r : ℝ} (hr0 : 0 < r) :
    HasDerivAt plusPrimitive ((log ((1 + r) / 2) ^ 3 + log 2 ^ 3) / r) r := by
  have h1r : 0 < 1 + r := by linarith
  have hw : HasDerivAt (fun r : ℝ ↦ 1 / (1 + r)) (-(1 / (1 + r) ^ 2)) r :=
    ((hasDerivAt_const r (1 : ℝ)).div ((hasDerivAt_id' r).const_add 1) h1r.ne').congr_deriv
      (by ring)
  have hw0 : 1 / (1 + r) ≠ 0 := by positivity
  have hw1 : |1 / (1 + r)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one h1r]
    linarith
  have hL : HasDerivAt (fun r : ℝ ↦ log (1 + r)) (1 / (1 + r)) r :=
    ((hasDerivAt_id r).const_add 1).log h1r.ne'
  have hlogr : HasDerivAt log r⁻¹ r := hasDerivAt_log hr0.ne'
  have h2 := (Dilog.hasDerivAt_Lir_two hw1 hw0).comp r hw
  have h3 := (Dilog.hasDerivAt_Lir_succ 2 hw1 hw0).comp r hw
  have h4 := (Dilog.hasDerivAt_Lir_succ 3 hw1 hw0).comp r hw
  have hl := (hasDerivAt_const r (log 2)).sub hL
  have hsum := (((((hl.pow 4).div_const 4).sub (hl.const_mul (log 2 ^ 3))).add
    (((hlogr.mul hL).sub (hL.pow 2)).mul
      (((hl.pow 2).add (hl.mul_const (log 2))).add_const (log 2 ^ 2)))).sub
    (((hl.pow 2).const_mul 3).mul h2)).add ((hl.const_mul 6).mul h3) |>.sub (h4.const_mul 6)
  unfold plusPrimitive
  refine hsum.congr_deriv ?_
  have hlog1 : log (1 - 1 / (1 + r)) = log r - log (1 + r) := by
    rw [show 1 - 1 / (1 + r) = r / (1 + r) by field_simp; ring, log_div hr0.ne' h1r.ne']
  have hlog2 : log ((1 + r) / 2) = log (1 + r) - log 2 := log_div h1r.ne' two_ne_zero
  simp only [Function.comp_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd, pow_one]
  rw [hlog1, hlog2]
  field_simp
  ring

/-- `plusPrimitive` is continuous on `[0, 1]`. -/
public theorem continuousOn_plusPrimitive : ContinuousOn plusPrimitive (Icc 0 1) := by
  have hne : ∀ r ∈ Icc (0 : ℝ) 1, 1 + r ≠ 0 := fun r hr ↦ by linarith [hr.1]
  have hq : ContinuousOn (fun r : ℝ ↦ log (1 + r)) (Icc 0 1) :=
    (continuousOn_const.add continuousOn_id).log hne
  have hpq : ContinuousOn (fun r : ℝ ↦ log r * log (1 + r)) (Icc 0 1) :=
    Arctan.continuous_log_mul_log_one_add.continuousOn
  have hw : ContinuousOn (fun r : ℝ ↦ 1 / (1 + r)) (Icc 0 1) :=
    continuousOn_const.div (continuousOn_const.add continuousOn_id) hne
  have hmaps : MapsTo (fun r : ℝ ↦ 1 / (1 + r)) (Icc 0 1) (Icc (-1) 1) := by
    intro r hr
    have h1r : 0 < 1 + r := by linarith [hr.1]
    refine ⟨by have : 0 < 1 / (1 + r) := by positivity
               linarith, ?_⟩
    rw [div_le_one h1r]
    linarith [hr.1]
  have hLi : ∀ s : ℕ, 2 ≤ s → ContinuousOn (fun r ↦ Lir s (1 / (1 + r))) (Icc 0 1) :=
    fun s hs ↦ (Dilog.continuousOn_Lir hs).comp hw hmaps
  have hl : ContinuousOn (fun r : ℝ ↦ log 2 - log (1 + r)) (Icc 0 1) := continuousOn_const.sub hq
  unfold plusPrimitive
  exact ((((((hl.pow 4).div_const 4).sub (continuousOn_const.mul hl)).add
    ((hpq.sub (hq.pow 2)).mul (((hl.pow 2).add (hl.mul continuousOn_const)).add
      continuousOn_const))).sub ((continuousOn_const.mul (hl.pow 2)).mul (hLi 2 le_rfl))).add
    ((continuousOn_const.mul hl).mul (hLi 3 (by norm_num)))).sub
    (continuousOn_const.mul (hLi 4 (by norm_num)))

/-- `(log³((1+r)/2) + log³ 2)/r ≥ 0` for `r > 0`. -/
public theorem log_cube_one_add_div_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ (log ((1 + r) / 2) ^ 3 + log 2 ^ 3) / r := by
  refine div_nonneg ?_ hr.le
  set x := log ((1 + r) / 2)
  set c := log 2
  have hx : -c ≤ x := by
    have : log (1 / 2) ≤ x := log_le_log (by norm_num) (by linarith)
    rwa [one_div, log_inv] at this
  have h1 : 0 ≤ x + c := by linarith
  have h2 : 0 ≤ x ^ 2 - x * c + c ^ 2 := by nlinarith [sq_nonneg (x - c / 2), sq_nonneg c]
  have : x ^ 3 + c ^ 3 = (x + c) * (x ^ 2 - x * c + c ^ 2) := by ring
  rw [this]
  exact mul_nonneg h1 h2

/-- `(log³((1+r)/2) + log³ 2)/r` is integrable on `[0, 1]`. -/
public theorem intervalIntegrable_log_cube_one_add_div :
    IntervalIntegrable (fun r ↦ (log ((1 + r) / 2) ^ 3 + log 2 ^ 3) / r) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact intervalIntegral.integrableOn_deriv_of_nonneg continuousOn_plusPrimitive
    (fun r hr ↦ hasDerivAt_plusPrimitive hr.1) fun r hr ↦ log_cube_one_add_div_nonneg hr.1

/-- `∫₀¹ (log³((1+r)/2) + log³ 2)/r dr
= π⁴/15 - 6 log 2 ζ(3) + (π²/2) log² 2 - log⁴ 2/4 - 6 Li₄(1/2)`. -/
public theorem integral_log_cube_one_add_div :
    ∫ r in (0 : ℝ)..1, (log ((1 + r) / 2) ^ 3 + log 2 ^ 3) / r =
      π ^ 4 / 15 - 6 * log 2 * zeta3 + π ^ 2 / 2 * log 2 ^ 2 - log 2 ^ 4 / 4
        - 6 * Lir 4 (1 / 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one continuousOn_plusPrimitive
    (fun r hr ↦ hasDerivAt_plusPrimitive hr.1) intervalIntegrable_log_cube_one_add_div]
  simp only [plusPrimitive, add_zero, log_one, log_zero, sub_zero, zero_mul, div_one,
    Dilog.Lir_two_one, Arctan.Lir_three_one, Lir_four_one, show (1 : ℝ) + 1 = 2 by norm_num,
    sub_self, one_div]
  ring

/-! ### The difference -/

/-- The integrand of the radial argument is integrable on `[0, 1]`. -/
public theorem intervalIntegrable_log_cube_div :
    IntervalIntegrable (fun r ↦ (log ((1 + r) / 2) ^ 3 - log ((1 - r) / 2) ^ 3) / r)
      volume 0 1 := by
  convert intervalIntegrable_log_cube_one_add_div.sub intervalIntegrable_log_cube_one_sub_div
    using 1
  ext r
  ring

/-- `∫₀¹ (log³((1+r)/2) - log³((1-r)/2))/r dr = 2π⁴/15 + π² log² 2 - log⁴ 2/4 - 6 Li₄(1/2)`. -/
public theorem integral_log_cube_div :
    ∫ r in (0 : ℝ)..1, (log ((1 + r) / 2) ^ 3 - log ((1 - r) / 2) ^ 3) / r =
      2 * π ^ 4 / 15 + π ^ 2 * log 2 ^ 2 - log 2 ^ 4 / 4 - 6 * Lir 4 (1 / 2) := by
  have h : (fun r ↦ (log ((1 + r) / 2) ^ 3 - log ((1 - r) / 2) ^ 3) / r) = fun r ↦
      (log ((1 + r) / 2) ^ 3 + log 2 ^ 3) / r - (log ((1 - r) / 2) ^ 3 + log 2 ^ 3) / r := by
    ext r
    ring
  rw [h, intervalIntegral.integral_sub intervalIntegrable_log_cube_one_add_div
    intervalIntegrable_log_cube_one_sub_div, integral_log_cube_one_add_div,
    integral_log_cube_one_sub_div]
  ring

end LeanPolyLog.LogSinSq
