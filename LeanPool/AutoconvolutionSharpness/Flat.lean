/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# The polynomials with flat antidiagonal square

This follows the construction of Crmarić, Kovač, and Rupčić, §2,
equations (1)–(3) of “Sharpness of the Martin–O'Bryant autoconvolution
inequality”. We use Mathlib's central - binomial recurrence and Cauchy
product for formal power series. A weighted antidiagonal induction
replaces the analytic notation for the binomial square root.
-/

@[expose] public section

open Finset Polynomial

namespace Autoconvolutions.Flat

noncomputable section

/-- The coefficient of degree `n` in the inverse square root of `1 - t`. -/
def weight (n : ℕ) : ℝ := n.centralBinom / (4 : ℝ) ^ n

theorem weight_pos (n : ℕ) : 0 < weight n := by
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos n) (by positivity)

private theorem weight_succ (n : ℕ) :
    ((n : ℝ) + 1) * weight (n + 1) = ((n : ℝ) + 1 / 2) * weight n := by
  have h : ((n : ℝ) + 1) * (n + 1).centralBinom =
      2 * (2 * (n : ℝ) + 1) * n.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold weight
  rw [pow_succ]
  field_simp
  linear_combination 2 * h

/-- The normalized central - binomial convolution. -/
theorem weight_convolution (n : ℕ) :
    ∑ p ∈ antidiagonal n, weight p.1 * weight p.2 = 1 := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    let L (p : ℕ × ℕ) := ((p.1 : ℝ) * weight p.1) * weight p.2
    let R (p : ℕ × ℕ) := weight p.1 * ((p.2 : ℝ) * weight p.2)
    have hL : ∑ p ∈ antidiagonal (n + 1), L p =
        ∑ p ∈ antidiagonal n, (((p.1 : ℝ) + 1 / 2) * weight p.1) * weight p.2 := by
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp [L, weight_succ]
    have hR : ∑ p ∈ antidiagonal (n + 1), R p =
        ∑ p ∈ antidiagonal n, weight p.1 * (((p.2 : ℝ) + 1 / 2) * weight p.2) := by
      rw [Finset.Nat.sum_antidiagonal_succ']
      simp [R, weight_succ]
    have h : ((n : ℝ) + 1) * (∑ p ∈ antidiagonal (n + 1), weight p.1 * weight p.2) =
        ((n : ℝ) + 1) * (∑ p ∈ antidiagonal n, weight p.1 * weight p.2) := by
      calc
        _ = ∑ p ∈ antidiagonal (n + 1), (L p + R p) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          have e : (p.1 : ℝ) + p.2 = (n : ℝ) + 1 := by
            exact_mod_cast Finset.mem_antidiagonal.mp hp
          rw [← e]
          dsimp [L, R]
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, hL, hR, ← Finset.sum_add_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          have e : (p.1 : ℝ) + p.2 = n := by
            exact_mod_cast Finset.mem_antidiagonal.mp hp
          rw [← e]
          ring
    exact (mul_left_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0) h).trans ih

/-- The formal series with coefficient `C (weight n) * x ^ n`. -/
def rootSeries (x : Polynomial ℝ) : PowerSeries (Polynomial ℝ) :=
  PowerSeries.mk (fun n => C (weight n) * x ^ n)

private theorem rootSeries_square_coeff (x : Polynomial ℝ) (n : ℕ) :
    PowerSeries.coeff n (rootSeries x * rootSeries x) = x ^ n := by
  rw [PowerSeries.coeff_mul]
  simp only [rootSeries, PowerSeries.coeff_mk]
  calc
    _ = ∑ p ∈ antidiagonal n, C (weight p.1 * weight p.2) * x ^ n := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [map_mul, ← Finset.mem_antidiagonal.mp hp, pow_add]
      ring
    _ = C (∑ p ∈ antidiagonal n, weight p.1 * weight p.2) * x ^ n := by
      rw [map_sum, Finset.sum_mul]
    _ = _ := by rw [weight_convolution, map_one, one_mul]

/-- The polynomial `P_i` of the paper. -/
def P (i : ℕ) : Polynomial ℝ :=
  PowerSeries.coeff i (rootSeries X * rootSeries 1)

theorem P_formula (i : ℕ) :
    P i = ∑ h ∈ range (i + 1), C (weight h * weight (i - h)) * X ^ h := by
  rw [P, PowerSeries.coeff_mul]
  simp only [rootSeries, PowerSeries.coeff_mk, one_pow, mul_one]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => C (weight a) * X ^ a * C (weight b)) i]
  apply Finset.sum_congr rfl
  intro h _
  rw [map_mul]
  ring

theorem P_eval_one (i : ℕ) : (P i).eval 1 = 1 := by
  rw [P_formula, Polynomial.eval_finsetSum]
  simpa using (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => weight a * weight b) i).symm.trans (weight_convolution i)

theorem P_coeff (i h : ℕ) :
    (P i).coeff h = if h ≤ i then weight h * weight (i - h) else 0 := by
  rw [P_formula, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]

theorem P_coeff_nonneg (i h : ℕ) : 0 ≤ (P i).coeff h := by
  rw [P_coeff]
  split
  · exact (mul_pos (weight_pos _) (weight_pos _)).le
  · exact le_rfl

/-- The exact square - root generating function identity in coefficient form. -/
theorem P_flat (s : ℕ) :
    ∑ p ∈ antidiagonal s, P p.1 * P p.2 =
      ∑ h ∈ range (s + 1), (X : Polynomial ℝ) ^ h := by
  let A := rootSeries X
  let B := rootSeries (1 : Polynomial ℝ)
  calc
    _ = PowerSeries.coeff s ((A * B) * (A * B)) := (PowerSeries.coeff_mul s (A * B) (A * B)).symm
    _ = PowerSeries.coeff s ((A * A) * (B * B)) := by congr 1; ring
    _ = ∑ p ∈ antidiagonal s, (X : Polynomial ℝ) ^ p.1 := by
      rw [PowerSeries.coeff_mul]
      simp only [A, B, rootSeries_square_coeff, one_pow, mul_one]
    _ = _ := Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a _ => X ^ a) s

/-- The truncated sum over `i + j=s`, with both indices at most `K`. -/
def B (K s : ℕ) : Polynomial ℝ :=
  ∑ p ∈ (antidiagonal s).filter (fun p => p.1 ≤ K ∧ p.2 ≤ K), P p.1 * P p.2

theorem B_flat {K s : ℕ} (hs : s ≤ K) :
    B K s = ∑ h ∈ range (s + 1), (X : Polynomial ℝ) ^ h := by
  have he : (antidiagonal s).filter (fun p => p.1 ≤ K ∧ p.2 ≤ K) = antidiagonal s := by
    ext p
    simp only [mem_filter, mem_antidiagonal, and_iff_left_iff_imp]
    omega
  rw [B, he, P_flat]

private theorem geom_coeff (s h : ℕ) :
    (∑ j ∈ range (s + 1), (X : Polynomial ℝ) ^ j).coeff h = if h ≤ s then 1 else 0 := by
  rw [Polynomial.finsetSum_coeff]
  simp [Polynomial.coeff_X_pow]

private theorem product_coeff_nonneg (i j h : ℕ) : 0 ≤ (P i * P j).coeff h := by
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (P_coeff_nonneg _ _) (P_coeff_nonneg _ _)

theorem B_coeff_nonneg (K s h : ℕ) : 0 ≤ (B K s).coeff h := by
  rw [B, Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun p _ => product_coeff_nonneg _ _ _

private theorem B_coeff_le_geom (K s h : ℕ) :
    (B K s).coeff h ≤ if h ≤ s then 1 else 0 := by
  rw [← geom_coeff, ← P_flat, B, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => product_coeff_nonneg _ _ _)

theorem B_coeff_le_one (K s h : ℕ) : (B K s).coeff h ≤ 1 := by
  apply (B_coeff_le_geom K s h).trans
  split <;> norm_num

theorem B_coeff_zero {K s h : ℕ} (hh : s < h) : (B K s).coeff h = 0 := by
  apply le_antisymm _ (B_coeff_nonneg K s h)
  simpa only [ite_eq_right (by omega : ¬h ≤ s)] using B_coeff_le_geom K s h

end

end Autoconvolutions.Flat
