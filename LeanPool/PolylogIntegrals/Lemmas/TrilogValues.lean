/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Proofs.A002
public import LeanPool.PolylogIntegrals.Lemmas.ArctanTrilog

/-!
# Special values for the trilogarithm integrals of A014

Values of `Li₂`, `Li₃` and `log` at the points `±i` and `(1 ± i)/2` of the closed unit disk, and
a few elementary facts shared by `LeanPolyLog.Lemmas.TrilogLogOneAddSq` and
`LeanPolyLog.Lemmas.TrilogLogSubLogSq`.

## Main results

* `LeanPolyLog.Trilog.Li_conj`: `Li_s(conj z) = conj (Li_s(z))`.
* `LeanPolyLog.Trilog.im_Li_three_I`, `LeanPolyLog.Trilog.im_Li_three_neg_I`:
  `Im Li₃(±i) = ±β(3) = ±π³/32`.
* `LeanPolyLog.Trilog.im_Li_three_one_sub_I_div_two`: `Im Li₃((1-i)/2) = -Im Li₃((1+i)/2)`.
* `LeanPolyLog.Trilog.im_Li_two_I`, `LeanPolyLog.Trilog.im_Li_two_one_sub_I_div_two`:
  `Im Li₂(i) = G` and `Im Li₂((1-i)/2) = (π/8) log 2 - G` (from A001 and A002).
* `LeanPolyLog.Trilog.log_one_sub_I_div_two`, `LeanPolyLog.Trilog.log_one_add_I_div_two`:
  `log((1 ∓ i)/2) = -½ log 2 ∓ (π/4) i`.
* `LeanPolyLog.Trilog.im_ofReal_div_sub_I`: `Im (a/(x - i)) = a/(1 + x²)` for real `a`, `x`; this
  is how `1/(1 + x²)` arises as an imaginary part.

## Proof sketch

* Conjugation commutes with the series, since `conj` is continuous and additive.
* `Im Li₃(i) = ∑ Im(iⁿ⁺¹)/(n+1)³`: the terms with `n` odd vanish and those with `n = 2k` are
  `(-1)ᵏ/(2k+1)³`, which sum to `β(3) = π³/32` (`LeanPolyLog.Arctan.hasSum_beta_three`).
* `(1 - i)/2 = (1/2)(1 - i)`, so its logarithm is `-log 2 + log(1 - i)`, and `(1 + i)/2` is its
  conjugate, whose argument `-π/4` is not `π`.
-/

open Real Set ComplexConjugate

namespace LeanPolyLog.Trilog

/-! ### Conjugation -/

/-- `Li_s(conj z) = conj (Li_s(z))`. -/
public theorem Li_conj (s : ℕ) (z : ℂ) : Li s (conj z) = conj (Li s z) := by
  unfold Li
  rw [Complex.conj_tsum]
  congr 1
  funext n
  simp

/-! ### Values of `Li₃` and `Li₂` -/

/-- `Im Li₃(i) = β(3) = π³/32`. -/
public theorem im_Li_three_I : (Li 3 Complex.I).im = π ^ 3 / 32 := by
  set f : ℕ → ℝ := fun n ↦ (Complex.I ^ (n + 1) / ((n : ℂ) + 1) ^ 3).im with hf
  have h : HasSum f (Li 3 Complex.I).im :=
    Complex.hasSum_im (Dilog.hasSum_Li (s := 3) (by norm_num) (z := Complex.I) (by simp))
  have he : HasSum (fun k ↦ f (2 * k)) (π ^ 3 / 32) := by
    convert Arctan.hasSum_beta_three using 1
    funext k
    simp only [hf]
    rw [pow_succ, pow_mul, Complex.I_sq]
    have : ((-1 : ℂ) ^ k * Complex.I / (((2 * k : ℕ) : ℂ) + 1) ^ 3) =
        (((-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 3 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.mul_I_im, Complex.ofReal_re]
  have ho : HasSum (fun k ↦ f (2 * k + 1)) 0 := by
    convert hasSum_zero with k
    simp only [hf]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, Complex.I_sq]
    have : ((-1 : ℂ) ^ (k + 1) / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ 3) =
        (((-1 : ℝ) ^ (k + 1) / (2 * (k : ℝ) + 2) ^ 3 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [this, Complex.ofReal_im]
  have h2 := he.even_add_odd ho
  rw [add_zero] at h2
  exact h.unique h2

/-- `Im Li₃(-i) = -π³/32`. -/
public theorem im_Li_three_neg_I : (Li 3 (-Complex.I)).im = -(π ^ 3 / 32) := by
  rw [← Complex.conj_I, Li_conj, Complex.conj_im, im_Li_three_I]

/-- `Im Li₃((1-i)/2) = -Im Li₃((1+i)/2)`. -/
public theorem im_Li_three_one_sub_I_div_two :
    (Li 3 ((1 - Complex.I) / 2)).im = -(Li 3 ((1 + Complex.I) / 2)).im := by
  have h : (1 - Complex.I) / 2 = conj ((1 + Complex.I) / 2) := by
    simp only [map_div₀, map_add, map_one, Complex.conj_I, map_ofNat]
    ring
  rw [h, Li_conj, Complex.conj_im]

/-- `1 - i ≠ 0`. -/
public theorem one_sub_I_ne_zero : (1 : ℂ) - Complex.I ≠ 0 := by
  intro h
  simpa using congrArg Complex.re h

/-- `(1-i)/2 = 1/(1+i)`. -/
public theorem one_sub_I_div_two : (1 - Complex.I) / 2 = 1 / (1 + Complex.I) := by
  have h1 : (1 : ℂ) + Complex.I ≠ 0 := by
    intro h
    simpa using congrArg Complex.re h
  field_simp
  linear_combination -Complex.I_sq

/-- `Im Li₂((1-i)/2) = (π/8) log 2 - G` (A002). -/
public theorem im_Li_two_one_sub_I_div_two :
    (Li 2 ((1 - Complex.I) / 2)).im = π / 8 * Real.log 2 - G := by
  rw [one_sub_I_div_two, Proofs.A002]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im]
  ring

/-- `Im Li₂(i) = G` (A001). -/
public theorem im_Li_two_I : (Li 2 Complex.I).im = G := by
  rw [Proofs.A001]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im]
  ring

/-! ### Values of `log` -/

/-- `log((1-i)/2) = -½ log 2 - (π/4) i`. -/
public theorem log_one_sub_I_div_two :
    Complex.log ((1 - Complex.I) / 2) =
      ((-(Real.log 2 / 2) : ℝ) : ℂ) - ((π / 4 : ℝ) : ℂ) * Complex.I := by
  rw [show (1 - Complex.I) / 2 = ((1 / 2 : ℝ) : ℂ) * (1 - Complex.I) by push_cast; ring,
    Complex.log_ofReal_mul (by norm_num) one_sub_I_ne_zero, Dilog.log_one_sub_I, one_div,
    Real.log_inv]
  push_cast
  ring

/-- `log((1+i)/2) = -½ log 2 + (π/4) i`. -/
public theorem log_one_add_I_div_two :
    Complex.log ((1 + Complex.I) / 2) =
      ((-(Real.log 2 / 2) : ℝ) : ℂ) + ((π / 4 : ℝ) : ℂ) * Complex.I := by
  have harg : Complex.arg ((1 - Complex.I) / 2) ≠ π := by
    rw [show (1 - Complex.I) / 2 = ((1 / 2 : ℝ) : ℂ) * (1 - Complex.I) by push_cast; ring,
      Complex.arg_real_mul _ (by norm_num), Dilog.arg_one_sub_I]
    linarith [pi_pos]
  have h : (1 + Complex.I) / 2 = conj ((1 - Complex.I) / 2) := by
    simp only [map_div₀, map_sub, map_one, Complex.conj_I, map_ofNat, sub_neg_eq_add]
  rw [h, Complex.log_conj _ harg, log_one_sub_I_div_two]
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-! ### Elementary facts -/

/-- `x - i ≠ 0` for real `x`. -/
public theorem ofReal_sub_I_ne_zero (x : ℝ) : (x : ℂ) - Complex.I ≠ 0 := by
  intro h
  simpa using congrArg Complex.im h

/-- `Im (a/(x - i)) = a/(1 + x²)` for real `a` and `x`. -/
public theorem im_ofReal_div_sub_I (a x : ℝ) :
    ((a : ℂ) / ((x : ℂ) - Complex.I)).im = a / (1 + x ^ 2) := by
  rw [Complex.div_im]
  simp [Complex.normSq_apply]
  ring

/-- `x ↦ log(1 + x)` is continuous on `[0, 1]`. -/
public theorem continuousOn_log_one_add : ContinuousOn (fun t : ℝ ↦ Real.log (1 + t)) (Icc 0 1) :=
  ContinuousOn.log (by fun_prop) fun t ht ↦ (by linarith [ht.1] : (0 : ℝ) < 1 + t).ne'

end LeanPolyLog.Trilog
