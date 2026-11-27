/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt imports and reformat the lower-rate proof. -/

module
public import LeanPool.VenNullClockRoundRates.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform lower masking rate under an observable mean budget. -/
@[expose] public section
noncomputable section
namespace VenRate
open MeasureTheory VenMask

/-- Every uniform error envelope on the actual unnormalized two-layer curves
obeys the eventual lower masking rate. The constants are chosen before the
alternative orientation, budget, and arbitrary separate nuisance profiles. -/
theorem lower_masking_rate (μ : Measure UnitSphere) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {d a b : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    ∃ C M₀ : ℝ, 0 < C ∧ 1 < M₀ ∧
    ∀ {M θ ε : ℝ} {w₀ w₁ : UnitSphere → ℝ},
      M₀ ≤ M → d ≤ 1 - Real.cos θ ^ 2 → Integrable w₀ μ → Integrable w₁ μ →
      (∀ᵐ y ∂μ, 1 ≤ w₀ y) → (∀ᵐ y ∂μ, 1 ≤ w₁ y) →
      (∫ y, w₀ y ∂μ) ≤ M → (∫ y, w₁ y ∂μ) ≤ M →
      DataClose μ w₀ w₁ θ b a ε →
      Real.exp (-C * Real.log M * Real.log (Real.log M)) ≤ ε := by
  obtain ⟨c, K, T, R, J, hc, hK, hR, hRT, _hT1, hJ, F⟩ := finite_layer_separation μ hd hd1 hb
  have hT := hR.trans hRT
  let D := Real.log T - Real.log R
  have hD : 0 < D := sub_pos.mpr (Real.log_lt_log hR hRT)
  let N := 2 / D + 1
  let m := min a 1
  let A := 1 + N / m
  let B := |Real.log A| + |Real.log T| + 1
  let L₀ := max (Real.exp 1) (max (Real.log K - Real.log (c / 2)) (Real.log J - Real.log (c / 2)))
  have hm : 0 < m := lt_min ha zero_lt_one
  have hN : 0 < N := by dsimp [N]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hL₀ : 0 < L₀ := (Real.exp_pos _).trans_le (le_max_left _ _)
  refine ⟨N * B + 1, Real.exp L₀, by positivity, Real.one_lt_exp_iff.mpr hL₀, ?_⟩
  intro M θ ε w₀ w₁ hM hθ i₀ i₁ f₀ f₁ m₀ m₁ H
  let L := Real.log M
  let l := Real.log L
  have hMp : 0 < M := (Real.exp_pos _).trans_le hM
  have hLL : L₀ ≤ L := (Real.le_log_iff_exp_le hMp).mpr hM
  have hL : 0 < L := hL₀.trans_le hLL
  have hel : Real.exp 1 ≤ L := (le_max_left _ _).trans hLL
  have h1 : 1 ≤ L := (Real.one_le_exp zero_le_one).trans hel
  have hl : 1 ≤ l := (Real.le_log_iff_exp_le hL).mpr hel
  have hKc : Real.log K - Real.log (c / 2) ≤ L := (le_max_left _ _).trans ((le_max_right _
    _).trans hLL)
  have hJc : Real.log J - Real.log (c / 2) ≤ L := (le_max_right _ _).trans ((le_max_right _
    _).trans hLL)
  let k := ⌈(2 / D) * L⌉₊
  have hlk : (2 / D) * L ≤ (k : ℝ) := Nat.le_ceil _
  have hkk : 0 < (k : ℝ) := (show 0 < (2 / D) * L by positivity).trans_le hlk
  have hk' : 1 ≤ k := by exact_mod_cast (show 0 < k by exact_mod_cast hkk)
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk'
  have hku : (k : ℝ) ≤ N * L := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (2 / D) * L by positivity)
    dsimp only [N, k]; linarith
  have hkd : 2 * L ≤ (k : ℝ) * D := by
    have v := mul_le_mul_of_nonneg_right hlk hD.le
    convert v using 1
    field_simp
  let h := m / (k : ℝ)
  have hhp : 0 < h := div_pos hm hkk
  have hh1 : h ≤ 1 := (div_le_iff₀ hkk).mpr (by rw [one_mul]; exact (min_le_right a 1).trans hk1)
  have hgrid : (k : ℝ) * h ≤ a := by
    dsimp [h]
    rw [mul_div_cancel₀ _ hkk.ne']
    exact min_le_left _ _
  have hfin := F k hθ hhp hh1 hgrid i₀ i₁ f₀ f₁ m₀ m₁ H
  have c2 : 0 < c / 2 := by positivity
  have htail : K * M * R ^ k ≤ (c / 2) * T ^ k := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by positivity : K * M ≠ 0) (pow_ne_zero _ hR.ne'),
      Real.log_mul hK.ne' hMp.ne', Real.log_mul c2.ne' (pow_ne_zero _ hT.ne'), Real.log_pow,
        Real.log_pow]
    dsimp only [D] at hkd
    dsimp only [L] at hKc hkd
    linarith only [hkd, hKc]
  have hcoef : (c / 2) * T ^ k ≤ J * (1 + 1 / h) ^ k * ε := by linarith only [hfin, htail]
  have hcpos : 0 < (c / 2) * T ^ k := by positivity
  have hZ : 0 < 1 + 1 / h := by positivity
  have hε : 0 < ε := pos_of_mul_pos_right (hcpos.trans_le hcoef) (by positivity)
  have hlogs := Real.log_le_log hcpos hcoef
  rw [Real.log_mul c2.ne' (pow_ne_zero _ hT.ne'), Real.log_pow,
    Real.log_mul (by positivity : J * (1 + 1 / h) ^ k ≠ 0) hε.ne', Real.log_mul hJ.ne'
      (pow_ne_zero _ hZ.ne'),
    Real.log_pow] at hlogs
  have hr : 1 / h=(k : ℝ) / m := by dsimp only [h]; field_simp
  have hZ' : 1 + 1 / h ≤ A * L := by
    rw [hr]; dsimp only [A]
    have hv := div_le_div_of_nonneg_right hku hm.le
    calc
      _ ≤ L + (N * L) / m := add_le_add h1 hv
      _ = _ := by ring
  have hlogZ := Real.log_le_log hZ hZ'
  rw [Real.log_mul hA.ne' hL.ne'] at hlogZ
  have hBnd : Real.log (1 + 1 / h) - Real.log T ≤ B * l := by
    have la := le_abs_self (Real.log A)
    have lt := neg_le_abs (Real.log T)
    have ea := mul_le_mul_of_nonneg_left hl (abs_nonneg (Real.log A))
    have et := mul_le_mul_of_nonneg_left hl (abs_nonneg (Real.log T))
    dsimp only [l, B] at *
    linarith only [hlogZ, la, lt, ea, et]
  have hprod := (mul_le_mul_of_nonneg_left hBnd hkk.le).trans
    (mul_le_mul_of_nonneg_right hku (mul_nonneg hB.le (by linarith)))
  have hlL := mul_le_mul_of_nonneg_left hl hL.le
  apply (Real.le_log_iff_exp_le hε).mp
  change -(N * B + 1) * L * l ≤ Real.log ε
  linarith only [hlogs, hprod, hJc, hlL]
end VenRate
end
