/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SmoothValueExceptional

/-! # Power margins and error absorption for Corollary 6 -/

@[expose] public section

namespace NairTenenbaum

theorem smooth_cutoff_one_lt {q κ z : ℝ} (hq : 0 < q) (hκ : 0 < κ)
    (hz : (2 : ℝ) ^ (κ / (2 * q)) ≤ z) : 1 < z :=
  (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).trans_le hz

theorem rpow_neg_le_smoothSaving {q κ z x : ℝ} (hq : 0 < q) (hκ : 0 < κ)
    (hx : 1 ≤ x) (hz : (2 : ℝ) ^ (κ / (2 * q)) ≤ z) :
    x ^ (-(3 * q)) ≤ Real.exp (-κ * Real.log x / Real.log z) := by
  have hz₁ := smooth_cutoff_one_lt hq hκ hz
  have hlogz : 0 < Real.log z := Real.log_pos hz₁
  have Hlog := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hz
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), div_mul_eq_mul_div] at Hlog
  have Hclear := (div_le_iff₀ (by positivity : 0 < 2 * q)).mp Hlog
  have hlog₂ : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have Hκ : κ / Real.log z ≤ 3 * q := by
    apply (div_le_iff₀ hlogz).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog₂ hκ.le]
  rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
  apply Real.exp_le_exp.mpr
  calc
    _ = -(3 * q * Real.log x) := by ring
    _ ≤ -((κ / Real.log z) * Real.log x) :=
      neg_le_neg (mul_le_mul_of_nonneg_right Hκ (Real.log_nonneg hx))
    _ = _ := by ring

/-- Absorb a small power-sized exceptional set while retaining the entire
smoothness saving permitted by the original lower cutoff. -/
theorem exists_smoothSaving_absorption (g : ℕ) {q : ℝ} (hq : 0 < q) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree ≤ g →
      ∀ (F : ArithmeticMap k), (∀ n, 0 ≤ F n) → ∀ (x y κ z : ℝ), 2 ≤ x →
      x ^ (4 * q) ≤ y → 0 < κ → (2 : ℝ) ^ (κ / (2 * q)) ≤ z →
      x ^ (7 * q / 8) * F 1 ≤
        K * Real.exp (-κ * Real.log x / Real.log z) * mainTerm P F x y := by
  obtain ⟨K, hK, H⟩ := exists_powerSaving_le_mainTerm g (δ := q / 8) (by positivity)
  refine ⟨K, hK, ?_⟩
  intro k r P hdeg F hF x y κ z hx hy hκ hz
  have hx₀ : 0 < x := by linarith
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg hx₀.le _).trans hy
  have Hmain := H k r P hdeg F hF x y hx hy₀
  have Hsave := rpow_neg_le_smoothSaving hq hκ (by linarith : 1 ≤ x) hz
  calc
    _ = x ^ (4 * q) * x ^ (-(3 * q)) * x ^ (-(q / 8)) * F 1 := by
      rw [← Real.rpow_add hx₀, ← Real.rpow_add hx₀]
      congr 2
      ring
    _ ≤ y * x ^ (-(3 * q)) * x ^ (-(q / 8)) * F 1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hy (Real.rpow_nonneg hx₀.le _)) (Real.rpow_nonneg hx₀.le _))
            (hF 1)
    _ = x ^ (-(3 * q)) * (y * x ^ (-(q / 8)) * F 1) := by ring
    _ ≤ x ^ (-(3 * q)) * (K * mainTerm P F x y) :=
      mul_le_mul_of_nonneg_left Hmain (Real.rpow_nonneg hx₀.le _)
    _ ≤ Real.exp (-κ * Real.log x / Real.log z) * (K * mainTerm P F x y) :=
      mul_le_mul_of_nonneg_right Hsave (mul_nonneg (by linarith) (mainTerm_nonneg P hF x hy₀))
    _ = _ := by ring

theorem smooth_value_growth_margin {g : ℕ} (hg : 0 < g) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ((g : ℝ) + 1 / δ + 1) * (ε * δ / 4) ≤ 3 * ((g : ℝ) ^ 2 * ε) / 4 := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have Heq : ((g : ℝ) + 1 / δ + 1) * (ε * δ / 4) = ε * ((g : ℝ) * δ + 1 + δ) / 4 := by
    field_simp
  rw [Heq]
  have H : (g : ℝ) * δ + 1 + δ ≤ 3 * (g : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hδ₁ (by linarith : (0 : ℝ) ≤ g)]
  nlinarith [mul_le_mul_of_nonneg_left H hε]

theorem PolynomialSystem.shortInterval_value_bound {k r : ℕ} (P : PolynomialSystem k r)
    {g : ℕ} (hdeg : P.total.natDegree = g) {x y δ : ℝ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) (hyx : y ≤ x) (hδ : 0 < δ)
    (hheight : (polynomialHeight P.total : ℝ) ^ δ ≤ x)
    (hlarge : ((g : ℝ) + 1) * 2 ^ g ≤ x) :
    ∀ n ∈ shortInterval x y, ((P.total.eval (n : ℤ)).natAbs : ℝ) ≤ x ^ ((g : ℝ) + 1 / δ + 1) := by
  intro n hn
  apply eval_natAbs_le_rpow_of_height hdeg hx hδ hheight hlarge
  simp only [Int.natAbs_natCast]
  have Hn : (n : ℝ) ≤ x + y := (Nat.le_floor_iff (by
    linarith : 0 ≤ x + y)).mp (Finset.mem_Ioc.mp hn).2
  linarith

end NairTenenbaum
