/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Arithmetic.Parameters
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
Explicit decay sequences for the corrected iteration. States are indexed from zero; their
small parameters correspond to the next paper step. The recurrence uses the exponent 3 / 2.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963
namespace Iteration

/-- Superexponential decay with exponent `(3/2)^s`. -/
def decay (x : ℝ≥0) (s : ℕ) : ℝ≥0 := x ^ ((3 / 2 : ℝ) ^ s)

@[simp] theorem decay_zero (x : ℝ≥0) : decay x 0 = x := by simp [decay]

theorem decay_succ (x : ℝ≥0) (s : ℕ) :
    decay x (s + 1) = decay x s ^ (3 / 2 : ℝ) := by
  simp only [decay, pow_succ, NNReal.rpow_mul]

theorem decay_pos {x : ℝ≥0} (hx : 0 < x) (s : ℕ) : 0 < decay x s :=
  NNReal.rpow_pos hx

theorem decay_add (x : ℝ≥0) (s t : ℕ) : decay x (s + t) = decay (decay x s) t := by
  simp only [decay, pow_add, NNReal.rpow_mul]

theorem coe_decay_succ (x : ℝ≥0) (s : ℕ) :
    (decay x (s + 1) : ℝ) = (decay x s : ℝ) * Real.sqrt (decay x s) := by
  rw [decay_succ, NNReal.coe_rpow, Real.sqrt_eq_rpow]
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add_of_nonneg (decay x s).coe_nonneg (by norm_num) (by norm_num), Real.rpow_one]

theorem decay_le {x : ℝ≥0} (hx : x ≤ 1) (s : ℕ) : decay x s ≤ x := by
  exact NNReal.rpow_le_self_of_le_one hx (one_le_pow₀ (by norm_num))

theorem decay_half {x : ℝ≥0} (hx : x ≤ 1 / 4) (s : ℕ) :
    (decay x (s + 1) : ℝ) ≤ (decay x s : ℝ) / 2 := by
  have hd : (decay x s : ℝ) ≤ 1 / 4 :=
    (decay_le (hx.trans (by
      exact_mod_cast (show (1 / 4 : ℝ) ≤ 1 by norm_num))) s).trans hx
  have hs : Real.sqrt (decay x s) ≤ 1 / 2 :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith⟩
  rw [coe_decay_succ]
  nlinarith [(decay x s).coe_nonneg]

theorem decay_geometric {x : ℝ≥0} (hx : x ≤ 1 / 4) (s : ℕ) :
    (decay x s : ℝ) ≤ (x : ℝ) * (1 / 2 : ℝ) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hh := decay_half hx s
    rw [pow_succ]
    nlinarith

theorem decay_summable {x : ℝ≥0} (hx : x ≤ 1 / 4) :
    Summable (fun s => (decay x s : ℝ)) :=
  Summable.of_nonneg_of_le (fun s => (decay x s).coe_nonneg) (decay_geometric hx)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_left (x : ℝ))

theorem decay_tsum_le {x : ℝ≥0} (hx : x ≤ 1 / 4) :
    (∑' s, (decay x s : ℝ)) ≤ 2 * (x : ℝ) := by
  calc
    _ ≤ ∑' s, (x : ℝ) * (1 / 2 : ℝ) ^ s :=
      (decay_summable hx).tsum_le_tsum (decay_geometric hx)
        ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)).mul_left (x : ℝ))
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring

theorem decay_sum_le {x : ℝ≥0} (hx : x ≤ 1 / 4) (s : ℕ) :
    (∑ j ∈ Finset.range s, (decay x j : ℝ)) ≤ 2 * (x : ℝ) :=
  ((decay_summable hx).sum_le_tsum _ (fun _ _ => NNReal.coe_nonneg _)).trans
    (decay_tsum_le hx)

theorem decay_tail_le {x : ℝ≥0} (hx : x ≤ 1 / 4) (s : ℕ) :
    (∑' j, (decay x (s + j) : ℝ)) ≤ 2 * (decay x s : ℝ) := by
  simp only [decay_add]
  apply decay_tsum_le
  exact (decay_le (hx.trans (by
    exact_mod_cast (show (1 / 4 : ℝ) ≤ 1 by norm_num))) s).trans hx

/-- The stage's smallness parameter along the superexponential decay sequence. -/
def delta (δ₁ : ℝ≥0) (s : ℕ) : ℝ≥0 := decay δ₁ s
/-- The cubic smallness scale used for displacement and action-domain erosion. -/
def beta (δ₁ : ℝ≥0) (s : ℕ) : ℝ≥0 := delta δ₁ s ^ 3
/-- The stage's strip-loss scale derived from the initial smallness parameter. -/
def gamma (n : ℕ) (δ₁ : ℝ≥0) (s : ℕ) : ℝ≥0 :=
  decay (δ₁ ^ (1 / (4 * (n : ℝ)))) s
/-- The stage's perturbation bound chosen with the iteration exponent. -/
def perturbation (n : ℕ) (δ₁ : ℝ≥0) (s : ℕ) : ℝ :=
  (delta δ₁ s : ℝ) ^ iterationExponent n

theorem gamma_eq (n : ℕ) (δ₁ : ℝ≥0) (s : ℕ) :
    gamma n δ₁ s = delta δ₁ s ^ (1 / (4 * (n : ℝ))) := by
  simp only [gamma, delta, decay, ← NNReal.rpow_mul, mul_comm]

theorem gamma_pow {n : ℕ} (hn : 0 < n) (δ₁ : ℝ≥0) (s : ℕ) :
    gamma n δ₁ s ^ (4 * n) = delta δ₁ s := by
  rw [gamma_eq, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (1 / (4 * (n : ℝ))) * ((4 * n : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp [hn']
  rw [he, NNReal.rpow_one]

theorem gamma_initial_bounds {n : ℕ} (hn : 0 < n) {δ₁ ρ₀ : ℝ≥0} {κ : ℝ}
    (hδ : (δ₁ : ℝ) < threshold2 n κ ρ₀) :
    (gamma n δ₁ 0 : ℝ) < (ρ₀ : ℝ) / 10 ∧ (gamma n δ₁ 0 : ℝ) < 1 / 4 := by
  obtain ⟨hρ, h4, _⟩ := (show (δ₁ : ℝ) < ((10 : ℝ) ^ (4 * n))⁻¹ * (ρ₀ : ℝ) ^ (4 * n) ∧
      (δ₁ : ℝ) < ((4 : ℝ) ^ (4 * n))⁻¹ ∧ (δ₁ : ℝ) < κ by
    simpa only [threshold2, lt_min_iff] using hδ)
  have hp : (gamma n δ₁ 0 : ℝ) ^ (4 * n) = (δ₁ : ℝ) := by
    simp only [← NNReal.coe_pow, gamma_pow hn, delta, decay_zero]
  constructor
  · apply lt_of_pow_lt_pow_left₀ (4 * n) (by positivity : (0 : ℝ) ≤ (ρ₀ : ℝ) / 10)
    rw [hp, div_pow]
    simpa only [div_eq_mul_inv, mul_comm] using hρ
  · apply lt_of_pow_lt_pow_left₀ (4 * n) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [hp, div_pow, one_pow]
    simpa only [one_div] using h4

theorem delta_initial_lt_quarter {n : ℕ} {θ Θ ρ κ D : ℝ} {δ₁ : ℝ≥0}
    (hδ : (δ₁ : ℝ) < threshold5 n θ Θ ρ κ D) : δ₁ < 1 / 4 := by
  have hh := (threshold0_bounds (threshold1_bounds (threshold5_bounds hδ).1).1).1
  have : (δ₁ : ℝ) < 1 / 4 := by linarith
  exact_mod_cast this

theorem remainder_eq_next {δ₁ : ℝ≥0} (hδ : 0 < δ₁) (n s : ℕ) :
    (perturbation n δ₁ s) ^ 2 /
      ((delta δ₁ s : ℝ) ^ (2 * stepExponent n) * (beta δ₁ s : ℝ) ^ 2) =
      perturbation n δ₁ (s + 1) := by
  have hd : (0 : ℝ) < delta δ₁ s := decay_pos hδ s
  change ((delta δ₁ s : ℝ) ^ iterationExponent n) ^ 2 /
    ((delta δ₁ s : ℝ) ^ (2 * stepExponent n) * ((delta δ₁ s : ℝ) ^ 3) ^ 2) = _
  rw [budget_step_eq hd n]
  unfold perturbation delta
  rw [decay_succ, NNReal.coe_rpow]
  conv_rhs => rw [← Real.rpow_natCast, ← Real.rpow_mul (decay δ₁ s).coe_nonneg]
  have he : (3 / 2 : ℝ) * (iterationExponent n : ℝ) = ((12 * n + 36 : ℕ) : ℝ) := by
    simp only [iterationExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he, Real.rpow_natCast]

end Iteration
end KamProject.Arnold1963
