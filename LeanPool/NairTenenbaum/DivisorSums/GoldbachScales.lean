/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.DivisorSums.GoldbachSieve

/-! # Choosing the Goldbach sieve cutoff uniformly in the represented integer -/

@[expose] public section

namespace NairTenenbaum

open Finset

theorem goldbachCount_le_twice_length (N : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) :
    (goldbachCount N x y : ℝ) ≤ 2 * y := by
  have hcard : goldbachCount N x y ≤ (shortInterval x y).card := card_filter_le _ _
  have hfloor : ⌊x⌋₊ ≤ ⌊x + y⌋₊ := Nat.floor_mono (by linarith)
  have hxy : 0 ≤ x + y := by linarith
  have H : (goldbachCount N x y : ℝ) ≤ (⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := by
    have H' : goldbachCount N x y ≤ ⌊x + y⌋₊ - ⌊x⌋₊ := by
      simpa only [shortInterval, Nat.card_Ioc] using hcard
    exact_mod_cast H'
  linarith [Nat.floor_le hxy, Nat.lt_floor_add_one x]

theorem log_sq_le_rpow {t θ : ℝ} (ht : 1 ≤ t) (hθ : 0 < θ) :
    (Real.log t) ^ 2 ≤ t ^ (θ / 2) / (θ / 4) ^ 2 := by
  have H := pow_le_pow_left₀ (Real.log_nonneg ht)
    (Real.log_le_rpow_div (by linarith : 0 ≤ t) (by linarith : 0 < θ / 4)) 2
  rw [div_pow, ← Real.rpow_natCast (t ^ (θ / 4)) 2,
    ← Real.rpow_mul (by linarith : 0 ≤ t)] at H
  norm_num only [Nat.cast_ofNat] at H
  rw [show θ / 4 * 2 = θ / 2 by ring] at H
  exact H

/-- A polynomial lower bound for the interval length suffices. No relation
between the interval's starting point and `N` is needed for this sieve bound. -/
theorem exists_goldbach_power_length_bound {θ : ℝ} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 < N → ∀ (x y : ℝ), 0 ≤ x →
      (N : ℝ) ^ θ ≤ y → y ≤ x →
      (goldbachCount N x y : ℝ) ≤ C * (((N : ℝ) / N.totient) * y / (Real.log N) ^ 2) := by
  obtain ⟨K, hK, Hsieve⟩ := exists_goldbach_sieve_bound
  let α := θ / 18
  have hα : 0 < α := by dsimp [α]; positivity
  let T := Real.exp (16 / α)
  have hT : 1 ≤ T := Real.one_le_exp_iff.mpr (by positivity)
  let C₁ : ℝ := K * (1 / α ^ 2 + 1 / (θ / 4) ^ 2)
  let C₂ : ℝ := 2 * T ^ 2
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    have : 0 < K := by linarith
    positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro N hN x y hx hy hyx
  have hN₁ : (1 : ℝ) < N := by exact_mod_cast hN
  have hN₀ : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN₁
  have hlog₂ : 0 < (Real.log N) ^ 2 := sq_pos_of_pos hlog
  have hy₁ : 1 ≤ y := (Real.one_le_rpow hN₁.le hθ.le).trans hy
  have hratio : 1 ≤ (N : ℝ) / N.totient := by
    have H := totientTwist_one_le 1 (by omega : N ≠ 0)
    simpa only [totientTwist, pow_one] using H
  let M : ℝ := ((N : ℝ) / N.totient) * y / (Real.log N) ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hyM : y / (Real.log N) ^ 2 ≤ M := by
    apply div_le_div_of_nonneg_right _ hlog₂.le
    exact le_mul_of_one_le_left (by linarith) hratio
  by_cases hNT : T ≤ (N : ℝ)
  · let z : ℝ := (N : ℝ) ^ α
    have hz₀ : 0 < z := Real.rpow_pos_of_pos hN₀ _
    have hzlog : 16 ≤ Real.log z := by
      have H : 16 / α ≤ Real.log N := by
        simpa only [T, Real.log_exp] using Real.log_le_log (Real.exp_pos _) hNT
      rw [Real.log_rpow hN₀]
      nlinarith [(div_le_iff₀ hα).mp H]
    have hz₂ : 2 ≤ z := by
      have H := Real.add_one_le_exp (Real.log z)
      rw [Real.exp_log hz₀] at H
      linarith
    have hy₂ : 2 ≤ y := hz₂.trans ((Real.rpow_le_rpow_of_exponent_le hN₁.le
      (by dsimp [α]; linarith : α ≤ θ)).trans hy)
    have Hz := Hsieve N (by omega) x y z hx hy₂ hyx hz₂ hzlog
    have Hzmain : ((N : ℝ) / N.totient) * y / (Real.log z) ^ 2 = (1 / α ^ 2) * M := by
      rw [Real.log_rpow hN₀]
      dsimp [M]
      ring
    have Hzpower : z ^ (9 : ℝ) = (N : ℝ) ^ (θ / 2) := by
      rw [← Real.rpow_mul hN₀.le]
      congr 1
      dsimp [α]
      ring
    have Herror : (N : ℝ) ^ (θ / 2) ≤ (1 / (θ / 4) ^ 2) * M := by
      have Hsq := log_sq_le_rpow hN₁.le hθ
      have Hmul := mul_le_mul_of_nonneg_left Hsq (Real.rpow_nonneg hN₀.le (θ / 2))
      have Hpow : (N : ℝ) ^ (θ / 2) * (N : ℝ) ^ (θ / 2) = (N : ℝ) ^ θ := by
        rw [← Real.rpow_add hN₀]
        congr 1
        ring
      have Hmul' : (N : ℝ) ^ (θ / 2) * (Real.log N) ^ 2 ≤ y / (θ / 4) ^ 2 := by
        calc
          _ ≤ (N : ℝ) ^ (θ / 2) * ((N : ℝ) ^ (θ / 2) / (θ / 4) ^ 2) := Hmul
          _ = (N : ℝ) ^ θ / (θ / 4) ^ 2 := by rw [← mul_div_assoc, Hpow]
          _ ≤ _ := div_le_div_of_nonneg_right hy (sq_nonneg _)
      have Hdiv := (le_div_iff₀ hlog₂).mpr Hmul'
      calc
        _ ≤ (1 / (θ / 4) ^ 2) * (y / (Real.log N) ^ 2) := Hdiv.trans_eq (by ring)
        _ ≤ _ := mul_le_mul_of_nonneg_left hyM (by positivity)
    rw [Hzmain, Hzpower] at Hz
    have Hlarge : (goldbachCount N x y : ℝ) ≤ C₁ * M := by
      have H := Hz.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl Herror) (by
        linarith : 0 ≤ K))
      exact H.trans_eq (by dsimp [C₁]; ring)
    exact Hlarge.trans (mul_le_mul_of_nonneg_right (by linarith : C₁ ≤ C₁ + C₂) hM)
  · have hlogT : Real.log N ≤ T := by
      have H := Real.log_le_sub_one_of_pos hN₀
      linarith [lt_of_not_ge hNT]
    have Hsq : (Real.log N) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hlog.le hlogT 2
    have Hsmall : (goldbachCount N x y : ℝ) ≤ C₂ * M := by
      calc
        _ ≤ 2 * y := goldbachCount_le_twice_length N hx hy₁
        _ ≤ C₂ * (y / (Real.log N) ^ 2) := by
          dsimp [C₂]
          rw [← mul_div_assoc]
          apply (le_div_iff₀ hlog₂).mpr
          nlinarith [mul_le_mul_of_nonneg_right Hsq (by linarith : 0 ≤ 2 * y)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hyM hC₂
    exact Hsmall.trans (mul_le_mul_of_nonneg_right (by linarith : C₂ ≤ C₁ + C₂) hM)

end NairTenenbaum
