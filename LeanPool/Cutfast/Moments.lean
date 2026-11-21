/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Radial

/-!
# Moments of the Barenblatt profiles (exact formulas of Lemmas 3.1 and 4.1)
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace

namespace Cutfast

namespace Moments

lemma eq_of_log_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : log x = log y) : x = y :=
  log_injOn_pos hx hy h

/-- `Bᵐ` for the full-space profile, written in the form of `Cutfast.Radial`. -/
lemma fullBarenblatt_rpow_eq {d : ℕ} {p b m : ℝ} (hc : 0 < fullBarenblattConst d p b)
    (hb : 0 < b) :
    (fun x : E d ↦ fullBarenblatt d p b x ^ m) =
      fun x ↦ ‖x‖ ^ (0 : ℝ) * (fullBarenblattConst d p b + b * ‖x‖ ^ 2) ^ (-(p * m)) := by
  funext x
  rw [rpow_zero, one_mul, fullBarenblatt, ← rpow_mul (by positivity), neg_mul]

/-- `Bᵐ` for the compact profile, written in the form of `Cutfast.Radial`. -/
lemma compactBarenblatt_rpow_eq {d : ℕ} {p b m : ℝ} :
    (fun x : E d ↦ compactBarenblatt d p b x ^ m) =
      fun x ↦ ‖x‖ ^ (0 : ℝ) * (max (compactBarenblattConst d p b - b * ‖x‖ ^ 2) 0) ^ (p * m) := by
  funext x
  rw [rpow_zero, one_mul, compactBarenblatt, ← rpow_mul (le_max_right _ _)]

/-- `‖x‖²` as a real power, to apply `Cutfast.Radial` with `a = 2`. -/
lemma norm_sq_mul_eq {d : ℕ} (f : E d → ℝ) :
    (fun x : E d ↦ ‖x‖ ^ 2 * f x) = fun x ↦ ‖x‖ ^ (2 : ℝ) * f x := by
  funext x
  rw [rpow_two]

end Moments

open Moments

theorem fullBarenblattConst_pos {d : ℕ} {p b : ℝ} (hp : (d : ℝ) / 2 < p) (hb : 0 < b) :
    0 < fullBarenblattConst d p b := by
  have h0 : (0 : ℝ) ≤ d / 2 := by positivity
  have h1 : 0 < Gamma (p - d / 2) := Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Gamma p := Gamma_pos_of_pos (by linarith)
  unfold fullBarenblattConst
  positivity

theorem compactBarenblattConst_pos {d : ℕ} {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    0 < compactBarenblattConst d p b := by
  have h0 : (0 : ℝ) ≤ d / 2 := by positivity
  have h1 : 0 < Gamma (p + 1 + d / 2) := Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Gamma (p + 1) := Gamma_pos_of_pos (by linarith)
  unfold compactBarenblattConst
  positivity

theorem integrable_fullBarenblatt_moment {d : ℕ} (hd : 1 ≤ d) {p b a : ℝ}
    (hp : (d : ℝ) / 2 < p) (hb : 0 < b) (ha0 : -(d : ℝ) < a) (ha : a < 2 * p - d) :
    Integrable (fun x : E d => ‖x‖ ^ a * fullBarenblatt d p b x) :=
  integrable_rpow_norm_mul_add_sq_rpow_neg hd ha0 (by linarith)
    (fullBarenblattConst_pos hp hb) hb

/-- Lemma 3.1, eq. (Bac). -/
theorem fullBarenblatt_moment' {d : ℕ} (hd : 1 ≤ d) {p b a : ℝ} (hp : (d : ℝ) / 2 < p)
    (hb : 0 < b) (ha0 : -(d : ℝ) < a) (ha : a < 2 * p - d) :
    ∫ x, ‖x‖ ^ a * fullBarenblatt d p b x =
      (π ^ ((d : ℝ) / 2) * Gamma (p - d / 2) / (b ^ p * Gamma p)) ^ (a / (2 * p - d)) *
        (Gamma ((d + a) / 2) * Gamma (p - (d + a) / 2) / (Gamma (d / 2) * Gamma (p - d / 2))) := by
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc := fullBarenblattConst_pos hp hb
  unfold fullBarenblatt
  rw [integral_rpow_norm_mul_add_sq_rpow_neg hd ha0 (by linarith) hc hb]
  unfold fullBarenblattConst
  have g1 : 0 < Gamma ((d + a) / 2) := Gamma_pos_of_pos (by linarith)
  have g2 : 0 < Gamma (p - (d + a) / 2) := Gamma_pos_of_pos (by linarith)
  have g3 : 0 < Gamma (d / 2) := Gamma_pos_of_pos (by positivity)
  have g4 : 0 < Gamma p := Gamma_pos_of_pos (by linarith)
  have g5 : 0 < Gamma (p - d / 2) := Gamma_pos_of_pos (by linarith)
  have he : 2 * p - d ≠ 0 := by linarith
  generalize Gamma ((d + a) / 2) = G1 at g1 ⊢
  generalize Gamma (p - (d + a) / 2) = G2 at g2 ⊢
  generalize Gamma (d / 2) = G3 at g3 ⊢
  generalize Gamma p = G4 at g4 ⊢
  generalize Gamma (p - d / 2) = G5 at g5 ⊢
  apply eq_of_log_eq (by positivity) (by positivity)
  simp (disch := positivity) only [log_mul, log_div, log_rpow]
  field_simp
  ring

theorem integrable_fullBarenblatt_rpow {d : ℕ} (hd : 1 ≤ d) {p b m : ℝ} (hm : 0 < m)
    (hp : (d : ℝ) / 2 < p) (hpm : (d : ℝ) / (2 * m) < p) (hb : 0 < b) :
    Integrable (fun x : E d => fullBarenblatt d p b x ^ m) := by
  have hc := fullBarenblattConst_pos hp hb
  have h2 : (d : ℝ) < p * (2 * m) := (div_lt_iff₀ (by positivity)).1 hpm
  rw [fullBarenblatt_rpow_eq hc hb]
  exact integrable_rpow_norm_mul_add_sq_rpow_neg hd
    (by simp only [Left.neg_neg_iff, Nat.cast_pos]; omega) (by linarith) hc hb

/-- Lemma 3.1, eq. (Bm). -/
theorem fullBarenblatt_integral_rpow' {d : ℕ} (hd : 1 ≤ d) {p b m : ℝ} (hm : 0 < m)
    (hp : (d : ℝ) / 2 < p) (hpm : (d : ℝ) / (2 * m) < p) (hb : 0 < b) :
    ∫ x, fullBarenblatt d p b x ^ m =
      (π / b) ^ (d * p * (1 - m) / (2 * p - d)) *
        (Gamma p / Gamma (p - d / 2)) ^ ((2 * p * m - d) / (2 * p - d)) *
        (Gamma (p * m - d / 2) / Gamma (p * m)) := by
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc := fullBarenblattConst_pos hp hb
  have h2 : (d : ℝ) < p * (2 * m) := (div_lt_iff₀ (by positivity)).1 hpm
  rw [fullBarenblatt_rpow_eq hc hb,
    integral_rpow_norm_mul_add_sq_rpow_neg hd
      (by simp only [Left.neg_neg_iff, Nat.cast_pos]; omega) (by linarith) hc hb]
  unfold fullBarenblattConst
  simp only [add_zero]
  have g1 : 0 < Gamma (p * m - d / 2) := Gamma_pos_of_pos (by linarith)
  have g3 : 0 < Gamma (d / 2) := Gamma_pos_of_pos (by positivity)
  have g4 : 0 < Gamma p := Gamma_pos_of_pos (by linarith)
  have g5 : 0 < Gamma (p - d / 2) := Gamma_pos_of_pos (by linarith)
  have g6 : 0 < Gamma (p * m) := Gamma_pos_of_pos (by nlinarith)
  have he : 2 * p - d ≠ 0 := by linarith
  generalize Gamma (p * m - d / 2) = G1 at g1 ⊢
  generalize Gamma (p * m) = G6 at g6 ⊢
  generalize Gamma (d / 2) = G3 at g3 ⊢
  generalize Gamma p = G4 at g4 ⊢
  generalize Gamma (p - d / 2) = G5 at g5 ⊢
  apply eq_of_log_eq (by positivity) (by positivity)
  simp (disch := positivity) only [log_mul, log_div, log_rpow]
  field_simp
  ring

theorem integrable_compactBarenblatt_moment {d : ℕ} (hd : 1 ≤ d) {p b a : ℝ} (hp : 0 < p)
    (hb : 0 < b) (ha : -(d : ℝ) < a) :
    Integrable (fun x : E d => ‖x‖ ^ a * compactBarenblatt d p b x) :=
  integrable_rpow_norm_mul_sub_sq_rpow hd ha hp (compactBarenblattConst_pos hp hb) hb

/-- The compact Barenblatt moment formula from Lemma 4.1, equation (4.2), extended to `a > -d`. -/
theorem compactBarenblatt_moment' {d : ℕ} (hd : 1 ≤ d) {p b a : ℝ} (hp : 0 < p) (hb : 0 < b)
    (ha : -(d : ℝ) < a) :
    ∫ x, ‖x‖ ^ a * compactBarenblatt d p b x =
      (Gamma (p + 1 + d / 2) / (π ^ ((d : ℝ) / 2) * b ^ p * Gamma (p + 1))) ^ (a / (d + 2 * p)) *
        (Gamma (p + 1 + d / 2) * Gamma ((d + a) / 2) /
          (Gamma (d / 2) * Gamma (p + 1 + (d + a) / 2))) := by
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc := compactBarenblattConst_pos (d := d) hp hb
  unfold compactBarenblatt
  rw [integral_rpow_norm_mul_sub_sq_rpow hd ha hp hc hb]
  unfold compactBarenblattConst
  have g1 : 0 < Gamma ((d + a) / 2) := Gamma_pos_of_pos (by linarith)
  have g2 : 0 < Gamma (p + 1) := Gamma_pos_of_pos (by linarith)
  have g3 : 0 < Gamma (d / 2) := Gamma_pos_of_pos (by positivity)
  have g4 : 0 < Gamma (p + 1 + (d + a) / 2) := Gamma_pos_of_pos (by linarith)
  have g5 : 0 < Gamma (p + 1 + d / 2) := Gamma_pos_of_pos (by positivity)
  have he : 2 * p + d ≠ 0 := by linarith
  have he' : d + 2 * p ≠ 0 := by linarith
  generalize Gamma ((d + a) / 2) = G1 at g1 ⊢
  generalize Gamma (p + 1 + (d + a) / 2) = G4 at g4 ⊢
  generalize Gamma (p + 1 + d / 2) = G5 at g5 ⊢
  generalize Gamma (p + 1) = G2 at g2 ⊢
  generalize Gamma (d / 2) = G3 at g3 ⊢
  apply eq_of_log_eq (by positivity) (by positivity)
  simp (disch := positivity) only [log_mul, log_div, log_rpow]
  field_simp
  ring

theorem integrable_compactBarenblatt_rpow {d : ℕ} (hd : 1 ≤ d) {p b m : ℝ} (hp : 0 < p)
    (hb : 0 < b) (hm : 0 < m) :
    Integrable (fun x : E d => compactBarenblatt d p b x ^ m) := by
  rw [compactBarenblatt_rpow_eq]
  exact integrable_rpow_norm_mul_sub_sq_rpow hd
    (by simp only [Left.neg_neg_iff, Nat.cast_pos]; omega) (by positivity)
    (compactBarenblattConst_pos hp hb) hb

/-- Lemma 4.1, eq. (Bmpme). -/
theorem compactBarenblatt_integral_rpow' {d : ℕ} (hd : 1 ≤ d) {p b m : ℝ} (hp : 0 < p)
    (hb : 0 < b) (hm : 0 < m) :
    ∫ x, compactBarenblatt d p b x ^ m =
      Gamma (p + 1 + d / 2) / Gamma (p * m + 1 + d / 2) * (Gamma (p * m + 1) / Gamma (p + 1)) *
        (b ^ ((d : ℝ) / 2) / π ^ ((d : ℝ) / 2) * (Gamma (p + 1 + d / 2) / Gamma (p + 1))) ^
          (2 * p * (m - 1) / (2 * p + d)) := by
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc := compactBarenblattConst_pos (d := d) hp hb
  have hpm : 0 < p * m := by positivity
  rw [compactBarenblatt_rpow_eq,
    integral_rpow_norm_mul_sub_sq_rpow hd
      (by simp only [Left.neg_neg_iff, Nat.cast_pos]; omega) hpm hc hb]
  unfold compactBarenblattConst
  simp only [add_zero]
  have g1 : 0 < Gamma (p * m + 1) := Gamma_pos_of_pos (by linarith)
  have g2 : 0 < Gamma (p + 1) := Gamma_pos_of_pos (by linarith)
  have g3 : 0 < Gamma (d / 2) := Gamma_pos_of_pos (by positivity)
  have g4 : 0 < Gamma (p * m + 1 + d / 2) := Gamma_pos_of_pos (by positivity)
  have g5 : 0 < Gamma (p + 1 + d / 2) := Gamma_pos_of_pos (by positivity)
  have he : 2 * p + d ≠ 0 := by linarith
  generalize Gamma (p * m + 1 + d / 2) = G4 at g4 ⊢
  generalize Gamma (p + 1 + d / 2) = G5 at g5 ⊢
  generalize Gamma (p * m + 1) = G1 at g1 ⊢
  generalize Gamma (p + 1) = G2 at g2 ⊢
  generalize Gamma (d / 2) = G3 at g3 ⊢
  apply eq_of_log_eq (by positivity) (by positivity)
  simp (disch := positivity) only [log_mul, log_div, log_rpow]
  field_simp
  ring

/-- For the Barenblatt exponents `p = 1/(1-m)`, `b = (1-m)/(2m)`, `m ∈ (d/(d+2), 1)`,
the second moment and the `Lᵐ` norm are related exactly by `∫ |x|² B = d ∫ Bᵐ`. -/
theorem fullBarenblatt_secondMoment_eq {d : ℕ} (hd : 1 ≤ d) {m : ℝ} (hm1 : m < 1)
    (hm2 : (d : ℝ) / (d + 2) < m) :
    ∫ x, ‖x‖ ^ 2 * fullBarenblatt d (1 / (1 - m)) ((1 - m) / (2 * m)) x =
      d * ∫ x, fullBarenblatt d (1 / (1 - m)) ((1 - m) / (2 * m)) x ^ m := by
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1m : 0 < 1 - m := by linarith
  have hm0 : 0 < m := lt_of_le_of_lt (by positivity) hm2
  have hm2' : (d : ℝ) < m * (d + 2) := (div_lt_iff₀ (by positivity)).1 hm2
  have hb : 0 < (1 - m) / (2 * m) := by positivity
  have hp : (d : ℝ) / 2 + 1 < 1 / (1 - m) := by
    rw [lt_div_iff₀ h1m]; nlinarith
  have hc := fullBarenblattConst_pos (d := d) (p := 1 / (1 - m)) (by linarith) hb
  have key : 1 / (1 - m) = 1 / (1 - m) * m + 1 := by field_simp; ring
  have hq : (d : ℝ) / 2 < 1 / (1 - m) * m := by linarith
  have hbq : (1 - m) / (2 * m) * (1 / (1 - m) * m) = 1 / 2 := by field_simp
  rw [norm_sq_mul_eq, fullBarenblatt_rpow_eq hc hb]
  simp only [fullBarenblatt]
  rw [integral_rpow_norm_mul_add_sq_rpow_neg hd (a := 2) (by linarith) (by linarith) hc hb,
    integral_rpow_norm_mul_add_sq_rpow_neg hd (a := 0) (by linarith) (by nlinarith) hc hb]
  generalize fullBarenblattConst d (1 / (1 - m)) ((1 - m) / (2 * m)) = c at hc ⊢
  generalize 1 / (1 - m) * m = q at key hbq hq ⊢
  rw [key]
  generalize (1 - m) / (2 * m) = b at hb hbq ⊢
  have hq0 : 0 < q := lt_of_le_of_lt (by positivity) hq
  have hbinv : b⁻¹ = 2 * q := by field_simp; linarith
  rw [show ((d : ℝ) + 2) / 2 - (q + 1) = d / 2 - q by ring,
    show q + 1 - ((d : ℝ) + 2) / 2 = q - d / 2 by ring,
    show ((d : ℝ) + 2) / 2 = d / 2 + 1 by ring, Gamma_add_one (s := (d : ℝ) / 2) (by positivity),
    Gamma_add_one hq0.ne', neg_add, rpow_add hb, rpow_neg_one, hbinv]
  simp only [add_zero]
  have g1 : 0 < Gamma (d / 2) := Gamma_pos_of_pos (by positivity)
  have g2 : 0 < Gamma q := Gamma_pos_of_pos hq0
  field_simp

/-- For the Barenblatt exponents `p = 1/(m-1)`, `b = (m-1)/(2m)`, `m > 1`,
the second moment and the `Lᵐ` norm are related exactly by `∫ |x|² B = d ∫ Bᵐ`. -/
theorem compactBarenblatt_secondMoment_eq {d : ℕ} (hd : 1 ≤ d) {m : ℝ} (hm1 : 1 < m) :
    ∫ x, ‖x‖ ^ 2 * compactBarenblatt d (1 / (m - 1)) ((m - 1) / (2 * m)) x =
      d * ∫ x, compactBarenblatt d (1 / (m - 1)) ((m - 1) / (2 * m)) x ^ m := by
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1m : 0 < m - 1 := by linarith
  have hm0 : 0 < m := by linarith
  have hb : 0 < (m - 1) / (2 * m) := by positivity
  have hp : 0 < 1 / (m - 1) := by positivity
  have hc := compactBarenblattConst_pos (d := d) hp hb
  have key : 1 / (m - 1) = 1 / (m - 1) * m - 1 := by field_simp; ring
  have hq : 0 < 1 / (m - 1) * m := by positivity
  have hbq : (m - 1) / (2 * m) * (1 / (m - 1) * m) = 1 / 2 := by field_simp
  rw [norm_sq_mul_eq, compactBarenblatt_rpow_eq]
  simp only [compactBarenblatt]
  rw [integral_rpow_norm_mul_sub_sq_rpow hd (a := 2) (by linarith) hp hc hb,
    integral_rpow_norm_mul_sub_sq_rpow hd (a := 0) (by linarith) hq hc hb]
  generalize compactBarenblattConst d (1 / (m - 1)) ((m - 1) / (2 * m)) = c at hc ⊢
  generalize 1 / (m - 1) * m = q at key hbq hq ⊢
  rw [key]
  generalize (m - 1) / (2 * m) = b at hb hbq ⊢
  have hbinv : b⁻¹ = 2 * q := by field_simp; linarith
  rw [show ((d : ℝ) + 2) / 2 + (q - 1) = d / 2 + q by ring,
    show q - 1 + 1 + ((d : ℝ) + 2) / 2 = q + 1 + d / 2 by ring, sub_add_cancel,
    show ((d : ℝ) + 2) / 2 = d / 2 + 1 by ring, Gamma_add_one (s := (d : ℝ) / 2) (by positivity),
    Gamma_add_one hq.ne', neg_add, rpow_add hb, rpow_neg_one, hbinv]
  simp only [add_zero]
  have g1 : 0 < Gamma (d / 2) := Gamma_pos_of_pos (by positivity)
  have g2 : 0 < Gamma (q + 1 + d / 2) := Gamma_pos_of_pos (by positivity)
  field_simp

end Cutfast
